#ifndef PACKETS_H
#define PACKETS_H

#include <stdint.h>

typedef struct ip_hdr 
{
    //ip-like
    uint8_t             version:4;
    uint8_t             ihl:4;
    uint8_t             tos;
    uint16_t            length;

    uint16_t            identification;
    uint16_t            offset;

    uint8_t             ttl;
    uint8_t             protocol;
    uint16_t            checksum;

    uint32_t            source_id;      // 4
    uint32_t            dest_id;        // 4

} __attribute__((__packed__)) ip_hdr_t;

typedef struct udp_hdr
{
    uint16_t            src_port;
    uint16_t            dst_port;
    uint16_t            length;
    uint16_t            checksum;
} __attribute__((__packed__)) udp_hdr_t;


typedef struct app_hdr
{ //QUIC-like
    uint64_t            connection_id;
    uint16_t            packet_num;
    uint16_t             frame_type; //frame_type 1: connection closing
} __attribute__((__packed__)) app_hdr_t;

typedef struct pkt_hdr
{
    ip_hdr_t  ip_hdr;
    udp_hdr_t udp_hdr;
    app_hdr_t app_hdr;
}  __attribute__((__packed__)) pkt_hdr_t;

#endif /* PACKETS_H */
