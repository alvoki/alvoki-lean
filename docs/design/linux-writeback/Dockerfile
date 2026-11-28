FROM alpine:3.24@sha256:f59abe656b692d901e184be3445e084786602108599d2a51d229c0f5a48c71bf AS guest
RUN --mount=type=secret,id=ca_bundle,target=/etc/ssl/certs/ca-certificates.crt \
    apk --no-cache add linux-virt=6.18.65-r0 e2fsprogs=1.47.4-r0 e2fsprogs-extra=1.47.4-r0 \
      xfsprogs=7.0.1-r0 device-mapper=2.03.35-r3 kmod=34.2-r1 cpio=2.15-r0 \
      gcc=15.2.0-r5 musl-dev=1.2.6-r3 linux-headers=7.0.0-r1
COPY probe.c /tmp/probe.c
COPY init /init
RUN cc -O2 -static -Wall -Wextra -Werror /tmp/probe.c -o /probe && chmod +x /init && \
    mkdir -p /guest && cp /boot/vmlinuz-virt /guest/kernel && \
    set -o pipefail && find /init /probe /bin /sbin /lib /usr /etc -xdev -print0 | \
      cpio --null -o -H newc | gzip -1 > /guest/initramfs

FROM alpine:3.24@sha256:f59abe656b692d901e184be3445e084786602108599d2a51d229c0f5a48c71bf
RUN --mount=type=secret,id=ca_bundle,target=/etc/ssl/certs/ca-certificates.crt \
    apk --no-cache add qemu-system-x86_64=11.0.3-r0
COPY --from=guest /guest /guest
