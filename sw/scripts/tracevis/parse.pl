sub flush_buffer {
    my $key = $_[0];
    my $buffer = $_[1];
    my $pcs = $_[2];
    my $binfile = $_[3];
    my $last_time = $_[4];
    my $inline = $_[5];
    my $use_pc_as_label = $_[6];
    my $format = $_[7];
    my $gvsoc = $_[8];

    my $linenum = $buffer =~ tr/\n//;

    if ($linenum < 2) { return; }

    #print $buffer;
    my $funcnames = `addr2line -e $binfile -f -a -i $pcs`;

    $funcnames = "$funcnames\n0x0"; # to let it process the last address in the below loop

    #print "$funcnames";

    #remove first line
    $funcnames =~ s/^[^\n]*\n//s;

    my @a2l_first_last_lines = {};
    $a2l_first_last_lines[0] = "";
    $a2l_first_last_lines[1] = "";  
    
    my @a2i_first_last_lines = {};
    $a2i_first_last_lines[0] = "";
    $a2i_first_last_lines[1] = "";  


    my $a2l_line_index = 1;
    if (!$inline) { $a2l_line_index = 0;}

    for (split /\n/, $funcnames) {
        my $a2l_line = $_;
        #print "$_\n";
        if ($a2l_line =~ /^(0x[0-9a-f]+)(.*)/ and $buffer =~ /.*\n.*\n.*/) {
            #print "ADDR: $1 $2\n";

            my $regex= qr/^\s+([0-9]+)\s+([0-9]+)\s+([0-9a-f]+)\s+[0-9a-f]+\s+([^ ]+)(.*)?\n/;
            if($gvsoc == 1) {
                #salvo: I might have broke it. I removed the "rest" group and merged it with "args", but I don't have a gvsoc trace to try out. :(
                $regex = qr/^\s*([0-9]+):\s+([0-9]+):\s+\[\e\[[0-9;]*m[^ ]*\s*\e\[[0-9;]*m\]\s+[^ ]+\s+M\s+([0-9a-f]+)\s+([^ ]+)(.*)?\n/;
            }

            my ($time, $cycles, $pc, $instr, $args) = $buffer =~ $regex;
    
            #remove current line from the buffer
            $buffer =~ s/^[^\n]*\n//s;

            my ($next_time, $next_cycles) = $buffer =~ /^\s+([0-9]+)\s+([0-9]+).*/;

            #print "$time - $cycles - $pc - $instr - $args\n";
            my $funcname = $a2l_first_last_lines[$a2l_line_index];
            my $coords = $a2i_first_last_lines[$a2l_line_index];
            my $duration_cycles = ($next_cycles - $cycles);
            my $duration_time = ($next_time - $time);            

            my $duration = $duration_time;
            my $start_time = $time;

            #my $start_time = $cycles;
            #my $duration = $duration_cycles;           

            my $label = $instr;
            if ($use_pc_as_label) { $label = "$pc - $instr"; }


            if ($format eq "json") {
                print "{\"name\": \"$label\", \"cat\": \"$instr\", \"ph\": \"X\", \"ts\": $start_time, \"dur\": $duration, \"pid\": \"$key\", \"tid\": \"$funcname\", \"args\":{\"pc\": \"$pc\", \"instr\": \"$instr $args\", \"time\": \"$cycles\", \"Origin\": \"$coords\"}},\n";
            } else {
                $coords =~ s/^(.*\/)+([^ ]*).*/$2/s;
                $instr =~ s/ +/ /;
                $args =~ s/ +/ /;
                $key =~ s/.*core_([0-9]+)_([0-9]+).*/$1 $2/s;
                print "$start_time $cycles $duration $key $funcname $pc $coords $instr \"$instr $args\"\n"   
            }
        
            $a2l_first_last_lines[0] = "";
            $a2l_first_last_lines[1] = "";
            $a2i_first_last_lines[0] = "";
            $a2i_first_last_lines[1] = "";
            $last_time = $start_time;

        } elsif ($a2l_line =~ /^[^\/].*/) {
            if ($a2l_first_last_lines[0] eq "") { $a2l_first_last_lines[0] = $a2l_line; }
            $a2l_first_last_lines[1] = $a2l_line;
        } else {
            if ($a2i_first_last_lines[0] eq "") { $a2i_first_last_lines[0] = $a2l_line; }
            $a2i_first_last_lines[1] = $a2l_line;
        }
        
    }
    #print "\n\nend flush\n\n";
    return $last_time;
}

sub convert_file {
    my $file = $_[0];
    my $binfile = $_[1];
    my $inline = $_[2];
    my $use_pc_as_label = $_[3];
    my $format = $_[4];
    my $gvsoc = $_[5];

    open my $info, $file or die "Could not open $file: $!";
    my $last_time = 0;
    my $buffer = "";
    my $pcs="";
    my $count = 0;

    while(my $line = <$info>) {

        my $regex = qr/^\s+([0-9]+)\s+([0-9]+)\s+([0-9a-f]+)\s+[0-9a-f]+\s+([^ ]+)\s+(.+?(?=  )).*/;
        if($gvsoc == 1) {
            $regex = qr/^\s*([0-9]+):\s+([0-9]+):\s+\[\e\[[0-9;]*m[^ ]*\s*\e\[[0-9;]*m\]\s+[^ ]+\s+M\s+([0-9a-f]+)\s+([^ ]+)\s+(.+?(?=  ))(.*)/;
        }
        if  ($line =~ $regex) {
            $buffer = "$buffer$line"; 
            $pcs = "$pcs $3";
            $count++;

            if ($count==1000){
                #print "flushing buffer\n";
                #print "$buffer";
                $last_time = flush_buffer($file, $buffer, $pcs, $binfile, $last_time, $inline, $use_pc_as_label, $format, $gvsoc);
#                print $last_time;
                #print "completed\n";
                $buffer="$line";
                $pcs="$3";
                $count=0;
            }
        }
    }

    #in case we didn't reach the flushing threshold
    #print "flushing buffer (last) Buffer:\n$buffer\n";
    $last_time = flush_buffer($file, $buffer, $pcs, $binfile, $last_time, $inline, $use_pc_as_label, $format, $gvsoc);
    #print "completed\n";
    close $info;
    return $last_time;
}

if ($#ARGV < 1) {
    print "Usage: $0 [-i] [-t] <bin_file> <trace_file_1> .. <trace_file_n>\n";
    exit;
}

my $arg_index = 0;

my $inline = 0;
my $format = "json";
my $use_pc_as_label = 0;
my $gvsoc = 0;

if ($ARGV[$arg_index] eq "-i") {
    $inline = 1;
    #$arg_index++;
    shift;
}

if ($ARGV[$arg_index] eq "-p") {
    $use_pc_as_label=1;
    #$arg_index++;
    shift;
}

if ($ARGV[$arg_index] eq "-t") {
    $format="txt";
    #$arg_index++;
    shift;
}

if ($ARGV[$arg_index] eq "-g") {
    $gvsoc=1;
    #$arg_index++;
    shift;
}

my $binfile=shift; #$ARGV[$arg_index++];

#print "$arg_index $inline $binfile\n";


if ($format eq "json") {
    print "{\"traceEvents\": [\n";
}

my $last_time=0;
foreach my $file (@ARGV) {
    $last_time = convert_file($file, $binfile, $inline, $use_pc_as_label, $format, $gvsoc);
}


#print "{\"name\": \"end\", \"cat\": \"end\", \"ph\": \"X\", \"ts\": $last_time, \"dur\": 0, \"pid\": \"$file\", \"tid\": \"end\", \"args\":{}}\n";

if ($format eq "json") {
    print "{}]}\n";
}

