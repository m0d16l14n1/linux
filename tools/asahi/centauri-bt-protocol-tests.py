#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-only
"""Host unit tests for Apple N1 Centauri Bluetooth protocol helpers.

Extracts and compiles the production ACL/SCO/ISO RX parsers, auxiliary ring
selection, LE event fixups and the set_bdaddr command from btcentauri.c.
"""
from pathlib import Path
import re
import subprocess
import tempfile

LEGACY_SRC = "drivers/bluetooth/btcentauri.c"


def extract_block(source, pattern):
    match = re.search(pattern, source, re.M)
    if not match:
        raise RuntimeError(f"missing pattern: {pattern}")
    brace = source.index("{", match.start())
    depth, end = 1, brace + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    if pattern.startswith(r"^struct ") or pattern.startswith(r"^static const "):
        end = source.index(";", end) + 1
    return source[match.start():end]


PRELUDE = r'''
#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint16_t __le16;
typedef struct { u8 b[6]; } bdaddr_t;

static bool is_zero_ether_addr(const u8 *a)
{
    return !(a[0] | a[1] | a[2] | a[3] | a[4] | a[5]);
}

static bool is_broadcast_ether_addr(const u8 *a)
{
    return (a[0] & a[1] & a[2] & a[3] & a[4] & a[5]) == 0xff;
}

#define ARRAY_SIZE(a) (sizeof(a) / sizeof((a)[0]))
#define HCI_ACL_HDR_SIZE 4
#define HCI_SCO_HDR_SIZE 3
#define HCI_ISO_HDR_SIZE 4
#define HCI_EVENT_HDR_SIZE 2
#define HCI_ACLDATA_PKT 0x02
#define HCI_SCODATA_PKT 0x03
#define HCI_ISODATA_PKT 0x05
#define HCI_EV_CMD_COMPLETE 0x0e
#define HCI_EV_LE_META 0x3e
#define HCI_EV_LE_EXT_ADV_REPORT 0x0d
#define HCI_OP_LE_READ_ACCEPT_LIST_SIZE 0x200f
#define LE_EXT_ADV_EVT_TYPE_MASK 0x001f
#define LE_EXT_ADV_LEGACY_PDU 0x0010
#define LE_EXT_ADV_SCAN_RSP 0x0008
#define LE_EXT_ADV_SCAN_IND 0x0002

#define CEN_RX_SLOTS 17
#define CEN_TX_SLOTS 5
#define CEN_LE_SLOTS 17

#define dev_warn_ratelimited(dev, fmt, ...) do { (void)(dev); if (0) printf(fmt, ##__VA_ARGS__); } while (0)
#define dev_warn_once(dev, fmt, ...) do { (void)(dev); if (0) printf(fmt, ##__VA_ARGS__); } while (0)
#define bt_dev_dbg(hdev, fmt, ...) ((void)(hdev))
#define bt_dev_info(hdev, fmt, ...) ((void)(hdev))
#define READ_ONCE(x) (x)

static u16 get_unaligned_le16(const void *p)
{
    const u8 *b = p;
    return (u16)b[0] | ((u16)b[1] << 8);
}

static void put_unaligned_le16(u16 v, void *p)
{
    u8 *b = p;
    b[0] = v & 0xff;
    b[1] = v >> 8;
}

static __attribute__((unused)) u16 le16_to_cpu(__le16 v) { return (u16)v; }
static __attribute__((unused)) __le16 cpu_to_le16(u16 v) { return (__le16)v; }

struct hci_ev_le_ext_adv_info {
    __le16 type;
    u8 bdaddr_type;
    u8 bdaddr[6];
    u8 primary_phy;
    u8 secondary_phy;
    u8 sid;
    u8 tx_power;
    int8_t rssi;
    __le16 interval;
    u8 direct_addr_type;
    u8 direct_addr[6];
    u8 length;
    u8 data[];
} __attribute__((packed));

struct sk_buff {
    u8 data[512];
    size_t len;
    u8 pkt_type;
};

struct sk_buff_head {
    unsigned int qlen;
};

static bool skb_queue_empty(const struct sk_buff_head *q) { return q->qlen == 0; }

struct hci_dev_stats {
    u32 byte_rx, err_rx;
};

struct hci_dev {
    struct hci_dev_stats stat;
};

struct pci_dev { int dev; };

static struct sk_buff *last_rx;
static unsigned int rx_count;
static u16 last_vendor_op;
static u8 last_vendor_data[16];
static u8 last_vendor_len;
static unsigned int vendor_calls;

static int cen_vendor_command(struct hci_dev *hdev, u16 opcode,
                              const void *data, u8 length)
{
    (void)hdev;
    assert(length <= sizeof(last_vendor_data));
    last_vendor_op = opcode;
    last_vendor_len = length;
    memcpy(last_vendor_data, data, length);
    vendor_calls++;
    return 0;
}

static struct sk_buff *bt_skb_alloc(unsigned int len, int gfp)
{
    (void)gfp;
    struct sk_buff *skb = calloc(1, sizeof(*skb));
    assert(skb && len <= sizeof(skb->data));
    return skb;
}
#define GFP_KERNEL 0

static void skb_put_data(struct sk_buff *skb, const void *data, unsigned int len)
{
    memcpy(skb->data + skb->len, data, len);
    skb->len += len;
}

#define hci_skb_pkt_type(skb) ((skb)->pkt_type)

static int hci_recv_frame(struct hci_dev *hdev, struct sk_buff *skb)
{
    (void)hdev;
    free(last_rx);
    last_rx = skb;
    rx_count++;
    return 0;
}

static bool accept_list;
static __attribute__((unused)) bool arm_auxiliary_rings = true;
static __attribute__((unused)) bool arm_le_data_rings = true;
static __attribute__((unused)) bool enable_acl = true;
'''

STRUCT_AND_TAIL = r'''
struct cen_aux_state {
    u32 offset, packets;
    u16 head, post;
    bool opened;
};

struct cen_bt {
    struct pci_dev *pdev;
    struct hci_dev *hdev;
    u16 mock_tail[16];
    struct sk_buff_head txq, acl_txq, le_txq, sco_txq, iso_txq;
    u16 tx_head, acl_tx_head, le_tx_head, sco_tx_head, iso_tx_head;
    u16 rx_head, le_rx_head;
    struct cen_aux_state aux[ARRAY_SIZE(cen_aux_specs)];
    u32 accept_list_hidden;
};

static u16 cen_tail(struct cen_bt *bt, u16 ring)
{
    return bt->mock_tail[ring];
}
'''

TESTS_LEGACY = r'''
int main(void)
{
    struct pci_dev pdev = {};
    struct hci_dev hdev = {};
    struct cen_bt bt = { .pdev = &pdev, .hdev = &hdev };

    /* 1. Resilient ACL RX delivery (valid, known attrs, unknown attr, malformed). */
    u8 acl1[] = { 0x02, 0x00, 0x02, 0x00, 0xca, 0xfe, 0x7f };
    cen_receive_acl(&bt, acl1, sizeof(acl1));
    assert(rx_count == 1 && last_rx->len == 6 && hdev.stat.err_rx == 0);

    u8 bad[] = { 0x02, 0x00, 0x20, 0x00, 0x01 };
    cen_receive_acl(&bt, bad, sizeof(bad));
    assert(rx_count == 1 && hdev.stat.err_rx == 1);

    /* 2. LE accept-list quirk on sk_buff. */
    struct sk_buff skb = { .len = 7 };
    u8 ev[7] = { HCI_EV_CMD_COMPLETE, 5, 1, 0x0f, 0x20, 0x00, 16 };
    memcpy(skb.data, ev, sizeof(ev));
    accept_list = false;
    cen_fixup_event(&bt, &skb);
    assert(skb.data[6] == 0 && bt.accept_list_hidden == 1);

    /* 3. Extended advertising legacy scan-response normalization. */
    struct sk_buff adv = {};
    adv.len = HCI_EVENT_HDR_SIZE + 2 + sizeof(struct hci_ev_le_ext_adv_info) + 2;
    adv.data[0] = HCI_EV_LE_META;
    adv.data[1] = adv.len - 2;
    adv.data[2] = HCI_EV_LE_EXT_ADV_REPORT;
    adv.data[3] = 1;
    struct hci_ev_le_ext_adv_info *info = (void *)(adv.data + 4);
    put_unaligned_le16(0x2718, &info->type);
    info->length = 2;
    cen_normalize_ext_adv(&adv);
    assert(get_unaligned_le16(&info->type) == 0x271a);

    /* 4. SCO and ISO RX framing (raw SCO, H4-prefixed ISO + ACL mux). */
    u8 sco1[] = { 0x05, 0x00, 0x03, 0xde, 0xad, 0xbe };
    cen_receive_sco(&bt, sco1, sizeof(sco1));
    assert(rx_count == 2 && last_rx->pkt_type == HCI_SCODATA_PKT && last_rx->len == 6);

    u8 iso1[] = { HCI_ISODATA_PKT, 0x20, 0x00, 0x02, 0x80, 0xfe, 0xed };
    cen_receive_iso(&bt, iso1, sizeof(iso1));
    assert(rx_count == 3 && last_rx->pkt_type == HCI_ISODATA_PKT && last_rx->len == 6);

    u8 iso_acl[] = { HCI_ACLDATA_PKT, 0x02, 0x00, 0x01, 0x00, 0x42 };
    cen_receive_iso(&bt, iso_acl, sizeof(iso_acl));
    assert(rx_count == 4 && last_rx->pkt_type == HCI_ACLDATA_PKT && last_rx->len == 5);

    assert(cen_aux_required(2) && cen_aux_required(3) && cen_aux_required(5));
    assert(cen_aux_required(8) && cen_aux_required(9) && cen_aux_required(11));
    assert(!cen_aux_required(12));

    /* 5. set_bdaddr sends BD_ADDR most significant byte first and rejects zero/broadcast. */
    bdaddr_t bd_ok = { .b = { 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0x02 } };
    bdaddr_t bd_zero = { .b = { 0, 0, 0, 0, 0, 0 } };
    bdaddr_t bd_bcast = { .b = { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff } };
    assert(cen_hci_set_bdaddr(&hdev, &bd_ok) == 0);
    assert(vendor_calls == 1 && last_vendor_op == 0xfc06 && last_vendor_len == 6);
    assert(memcmp(last_vendor_data, "\x02\xee\xdd\xcc\xbb\xaa", 6) == 0);
    assert(cen_hci_set_bdaddr(&hdev, &bd_zero) == -EINVAL);
    assert(cen_hci_set_bdaddr(&hdev, &bd_bcast) == -EINVAL);
    assert(vendor_calls == 1);

    free(last_rx);
    printf("PASS: t8142 Bluetooth protocol tests\n");
    return 0;
}
'''


def run_suite(label, src_path):
    source = src_path.read_text()
    pieces = [
        PRELUDE,
        extract_block(source, r"^struct cen_aux_spec \{"),
        extract_block(source, r"^static const struct cen_aux_spec cen_aux_specs\[\]"),
        STRUCT_AND_TAIL,
        extract_block(source, r"^static void cen_skip_rx_attrs\("),
        extract_block(source, r"^static void cen_receive_acl\("),
        extract_block(source, r"^static void cen_receive_sco\("),
        extract_block(source, r"^static void cen_receive_iso\("),
        extract_block(source, r"^static bool cen_aux_required\("),
        extract_block(source, r"^static void cen_fixup_event\("),
        extract_block(source, r"^static void cen_normalize_ext_adv\("),
        extract_block(source, r"^static int cen_hci_set_bdaddr\("),
        TESTS_LEGACY,
    ]
    with tempfile.TemporaryDirectory(prefix="centauri-bt-proto-") as tmp:
        c_file = Path(tmp) / "test.c"
        bin_file = Path(tmp) / "test"
        c_file.write_text("\n\n".join(pieces))
        subprocess.run(
            ["cc", "-std=gnu11", "-Wall", "-Wextra", "-Werror", "-Wno-unused-function", str(c_file), "-o", str(bin_file)],
            check=True,
        )
        subprocess.run([str(bin_file)], check=True)


def main():
    root = Path(__file__).resolve().parents[2]
    run_suite("t8142", root / LEGACY_SRC)


if __name__ == "__main__":
    main()
