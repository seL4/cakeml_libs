/*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <sel4/sel4.h>
#include <string.h>
#include <utils/util.h>

// FIXME: guard debug mode
#include <stdio.h>
#define DEBUG_INVOCATION(...) printf(__VA_ARGS__)

static const char *invocation_string(int label) {
#define CASE(inv) case inv: return #inv;
    switch(label) {
    CASE(InvalidInvocation)
    CASE(UntypedRetype)
    CASE(TCBReadRegisters)
    CASE(TCBWriteRegisters)
    CASE(TCBCopyRegisters)
    CASE(TCBConfigure)
    CASE(TCBSetPriority)
    CASE(TCBSetMCPriority)
    CASE(TCBSetSchedParams)
    CASE(TCBSetIPCBuffer)
    CASE(TCBSetSpace)
    CASE(TCBSuspend)
    CASE(TCBResume)
    CASE(TCBBindNotification)
    CASE(TCBUnbindNotification)
    CASE(TCBSetTLSBase)
    CASE(CNodeRevoke)
    CASE(CNodeDelete)
    CASE(CNodeCancelBadgedSends)
    CASE(CNodeCopy)
    CASE(CNodeMint)
    CASE(CNodeMove)
    CASE(CNodeMutate)
    CASE(CNodeRotate)
    CASE(CNodeSaveCaller)
    CASE(IRQIssueIRQHandler)
    CASE(IRQAckIRQ)
    CASE(IRQSetIRQHandler)
    CASE(IRQClearIRQHandler)
    CASE(DomainSetSet)
    CASE(ARMPDClean_Data)
    CASE(ARMPDInvalidate_Data)
    CASE(ARMPDCleanInvalidate_Data)
    CASE(ARMPDUnify_Instruction)
    CASE(ARMPageTableMap)
    CASE(ARMPageTableUnmap)
    CASE(ARMPageMap)
    CASE(ARMPageUnmap)
    CASE(ARMPageClean_Data)
    CASE(ARMPageInvalidate_Data)
    CASE(ARMPageCleanInvalidate_Data)
    CASE(ARMPageUnify_Instruction)
    CASE(ARMPageGetAddress)
    CASE(ARMASIDControlMakePool)
    CASE(ARMASIDPoolAssign)
    CASE(ARMIRQIssueIRQHandlerTrigger)
#undef CASE
    default: return "unknown invocation";
    }
};

#define FFI_SUCCESS 0

void ffiseL4_MessageInfo_new(unsigned char *c, long clen, unsigned char *a,
                             long alen)
{
    seL4_Word label;
    seL4_Word num_cap_words;
    seL4_Word num_input_words;

    int offset = 0;
    memcpy(&label, a + offset, sizeof(label));
    offset += sizeof(label);
    memcpy(&num_cap_words, a + offset, sizeof(num_cap_words));
    offset += sizeof(num_cap_words);
    memcpy(&num_input_words, a + offset, sizeof(num_input_words));

    seL4_MessageInfo_t msg =
        seL4_MessageInfo_new(label, 0, num_cap_words, num_input_words);

    memcpy(a, &msg, sizeof(msg));
}

void ffiseL4_CallWithMRs(unsigned char *c, long clen, unsigned char *a,
                         long alen)
{
    seL4_CPtr _service;
    seL4_MessageInfo_t tag;
    seL4_Word mr0;
    seL4_Word mr1;
    seL4_Word mr2;
    seL4_Word mr3;

    int offset = 0;
    memcpy(&_service, a + offset, sizeof(_service));
    offset += sizeof(_service);
    memcpy(&tag, a + offset, sizeof(tag));
    offset += sizeof(tag);
    memcpy(&mr0, a + offset, sizeof(mr0));
    offset += sizeof(mr0);
    memcpy(&mr1, a + offset, sizeof(mr1));
    offset += sizeof(mr1);
    memcpy(&mr2, a + offset, sizeof(mr2));
    offset += sizeof(mr2);
    memcpy(&mr3, a + offset, sizeof(mr3));

    DEBUG_INVOCATION("seL4_CallWithMRs(service=0x%zx, [label=%d(%s), caps=%d + %d, len=%d], MRs=0x%zx 0x%zx 0x%zx 0x%zx) ",
                     _service,
                     (int)seL4_MessageInfo_get_label(tag),
                     invocation_string(seL4_MessageInfo_get_label(tag)),
                     (int)seL4_MessageInfo_get_capsUnwrapped(tag),
                     (int)seL4_MessageInfo_get_extraCaps(tag),
                     (int)seL4_MessageInfo_get_length(tag),
                     mr0, mr1, mr2, mr3);

    seL4_MessageInfo_t output_tag =
        seL4_CallWithMRs(_service, tag, &mr0, &mr1, &mr2, &mr3);
    seL4_Error result = (seL4_Error)seL4_MessageInfo_get_label(output_tag);

    DEBUG_INVOCATION("   -->   0x%zx\n", result);

    offset = 0;
    memcpy(a + offset, &result, sizeof(result));
    offset += sizeof(result);
    memcpy(a + offset, &mr0, sizeof(mr0));
    offset += sizeof(mr0);
    memcpy(a + offset, &mr1, sizeof(mr1));
    offset += sizeof(mr1);
    memcpy(a + offset, &mr2, sizeof(mr2));
    offset += sizeof(mr2);
    memcpy(a + offset, &mr3, sizeof(mr3));
}

void ffiseL4_SetMR(unsigned char *c, long clen, unsigned char *a, long alen)
{
    seL4_Word reg_num;
    seL4_Word reg_val;

    int offset = 0;
    memcpy(&reg_num, a + offset, sizeof(reg_num));
    offset += sizeof(reg_num);
    memcpy(&reg_val, a + offset, sizeof(reg_val));

    seL4_SetMR(reg_num, reg_val);
}

void ffiseL4_SetCap(unsigned char *c, long clen, unsigned char *a, long alen)
{
    seL4_Word cap_num;
    seL4_CPtr cap_val;

    int offset = 0;
    memcpy(&cap_num, a + offset, sizeof(cap_num));
    offset += sizeof(cap_num);
    memcpy(&cap_val, a + offset, sizeof(cap_val));

    seL4_SetCap(cap_num, cap_val);
}

void ffiseL4_Recv(unsigned char *c, long clen, unsigned char *a, long alen)
{
    seL4_CPtr ep;
    memcpy(&ep, a + 1, sizeof(ep));
    seL4_Word badge;
    seL4_MessageInfo_t info = seL4_Recv(ep, &badge);
    seL4_Word len = seL4_MessageInfo_get_length(info) * sizeof(seL4_Word);
    int offset = 1;
    memcpy(a + offset, &len, sizeof(len));
    offset += sizeof(len);
    memcpy(a + offset, &badge, sizeof(badge));
    offset += sizeof(badge);
    memcpy(a + offset, &seL4_GetIPCBuffer()->msg[0], len);
    a[0] = FFI_SUCCESS;
}

void ffiseL4_ReplyRecv(unsigned char *c, long clen, unsigned char *a,
                       long alen)
{
    seL4_CPtr ep;
    int offset = 1;
    memcpy(&ep, a + offset, sizeof(ep));
    offset += sizeof(ep);
    seL4_Word len;
    memcpy(&len, a + offset, sizeof(len));
    offset += sizeof(len);
    seL4_Word badge;
    memcpy(&seL4_GetIPCBuffer()->msg[0], a + offset, len);
    seL4_MessageInfo_t info = seL4_ReplyRecv(
                                  ep,
                                  seL4_MessageInfo_new(
                                      0, 0, 0, ROUND_UP_UNSAFE(len, sizeof(seL4_Word)) / sizeof(seL4_Word)),
                                  &badge);
    len = seL4_MessageInfo_get_length(info) * sizeof(seL4_Word);
    offset = 1;
    memcpy(a + offset, &len, sizeof(len));
    offset += sizeof(len);
    memcpy(a + offset, &badge, sizeof(badge));
    offset += sizeof(badge);
    memcpy(a + offset, &seL4_GetIPCBuffer()->msg[0], len);
    a[0] = FFI_SUCCESS;
}

void ffiseL4_Send(unsigned char *c, long clen, unsigned char *a, long alen)
{
    seL4_CPtr ep;
    int offset = 1;
    memcpy(&ep, a + offset, sizeof(ep));
    offset += sizeof(ep);
    seL4_Word len;
    memcpy(&len, a + offset, sizeof(len));
    offset += sizeof(len);
    memcpy(&seL4_GetIPCBuffer()->msg[0], a + offset, len);
    seL4_Send(ep, seL4_MessageInfo_new(0, 0, 0,
                                       ROUND_UP_UNSAFE(len, sizeof(seL4_Word)) /
                                       sizeof(seL4_Word)));
    a[0] = FFI_SUCCESS;
}

// Wait on an seL4 notification or endpoint
void ffiseL4_Wait(unsigned char *c, long clen, unsigned char *a, long alen)
{
    seL4_CPtr src;
    memcpy(&src, a + 1, sizeof(src));
    seL4_Word badge;
    seL4_Wait(src, &badge);
    memcpy(a + 1, &badge, sizeof(badge));
    a[0] = FFI_SUCCESS;
}
