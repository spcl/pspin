../generic_driver/gdriver_args.c: ../generic_driver/gdriver_args.ggo
	gengetopt -i ../generic_driver/gdriver_args.ggo -F gdriver_args --output-dir=../generic_driver/

driver: driver/driver.c ../generic_driver/gdriver_args.c
	 gcc -std=c99 -I../generic_driver/ -I$(PSPIN_RT)/runtime/include/ -I$(PSPIN_HW)/verilator_model/include driver/driver.c ../generic_driver/gdriver.c ../generic_driver/gdriver_args.c -L$(PSPIN_HW)/verilator_model/lib/ -lpspin -o sim_${SPIN_APP_NAME}

driver_debug: driver/driver.c ../generic_driver/gdriver_args.c
	 gcc -g -std=c99 -I../generic_driver/ -I$(PSPIN_RT)/runtime/include/ -I$(PSPIN_HW)/verilator_model/include driver/driver.c ../generic_driver/gdriver.c ../generic_driver/gdriver_args.c -L$(PSPIN_HW)/verilator_model/lib/ -lpspin_debug -o sim_${SPIN_APP_NAME}_debug


all::
	make deploy
	make driver
	make driver_debug

clean::
	-@rm *.log 2>/dev/null || true
	-@rm -r build/ 2>/dev/null || true
	-@rm -r waves.vcd 2>/dev/null || true
	-@rm sim_${SPIN_APP_NAME} 2>/dev/null || true
	-@rm sim_${SPIN_APP_NAME}_debug 2>/dev/null || true