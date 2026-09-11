//! Port of the Falcon reference `rng.c`: the ChaCha20-based PRNG used by
//! the signature sampler. The output byte layout reproduces the AVX2
//! 8-way interleaving of the reference implementation bit-for-bit (this is
//! required for KAT reproducibility).

/// Reference `prng` structure: 64-byte state (key + IV + counter) and a
/// 1024-byte output buffer.
pub struct Prng {
    state: [u8; 64],
    buf: [u8; 1024],
    ptr: usize,
}

impl Prng {
    /// Reference `prng_init(p, src)`: draw 56 bytes from the (flipped)
    /// SHAKE256 context; bytes 0..48 are the key+IV, bytes 48..56 the block
    /// counter (little-endian).
    pub fn init(src: &mut super::common::InnerShake256) -> Self {
        let mut tmp = [0u8; 56];
        src.extract(&mut tmp);
        let mut state = [0u8; 64];
        state[..56].copy_from_slice(&tmp);
        // Counter: 8 bytes little-endian (state.d[48..56] read as u64 from
        // two little-endian u32 halves in the reference — identical here).
        let mut p = Self {
            state,
            buf: [0u8; 1024],
            ptr: 0,
        };
        p.refill();
        p
    }

    /// Reference `prng_refill`: regenerate the 1024-byte output buffer with
    /// eight ChaCha20 blocks (AVX2-style interleaving).
    pub fn refill(&mut self) {
        const CW: [u32; 4] = [0x6170_7865, 0x3320_646E, 0x7962_2D32, 0x6B20_6574];

        let mut cc = u64::from_le_bytes(self.state[48..56].try_into().unwrap());
        for u in 0..8usize {
            let mut state = [0u32; 16];
            state[0..4].copy_from_slice(&CW);
            for (i, word) in state[4..16].iter_mut().enumerate() {
                let b: [u8; 4] = self.state[i * 4..i * 4 + 4].try_into().unwrap();
                *word = u32::from_le_bytes(b);
            }
            state[14] ^= cc as u32;
            state[15] ^= (cc >> 32) as u32;
            for _ in 0..10 {
                qround(&mut state, 0, 4, 8, 12);
                qround(&mut state, 1, 5, 9, 13);
                qround(&mut state, 2, 6, 10, 14);
                qround(&mut state, 3, 7, 11, 15);
                qround(&mut state, 0, 5, 10, 15);
                qround(&mut state, 1, 6, 11, 12);
                qround(&mut state, 2, 7, 8, 13);
                qround(&mut state, 3, 4, 9, 14);
            }
            for v in 0..4 {
                state[v] = state[v].wrapping_add(CW[v]);
            }
            for v in 4..14 {
                let b: [u8; 4] = self.state[(v - 4) * 4..(v - 4) * 4 + 4].try_into().unwrap();
                state[v] = state[v].wrapping_add(u32::from_le_bytes(b));
            }
            state[14] = state[14].wrapping_add(
                u32::from_le_bytes(self.state[40..44].try_into().unwrap()) ^ (cc as u32),
            );
            state[15] = state[15].wrapping_add(
                u32::from_le_bytes(self.state[44..48].try_into().unwrap()) ^ ((cc >> 32) as u32),
            );
            cc = cc.wrapping_add(1);

            // AVX2-style interleaving of the 8 blocks.
            for v in 0..16usize {
                let bytes = state[v].to_le_bytes();
                let base = (u << 2) + (v << 5);
                self.buf[base..base + 4].copy_from_slice(&bytes);
            }
        }
        self.state[48..56].copy_from_slice(&cc.to_le_bytes());
        self.ptr = 0;
    }

    /// Reference `prng_get_bytes`.
    pub fn get_bytes(&mut self, out: &mut [u8]) {
        let mut done = 0usize;
        while done < out.len() {
            let avail = self.buf.len() - self.ptr;
            let clen = avail.min(out.len() - done);
            out[done..done + clen].copy_from_slice(&self.buf[self.ptr..self.ptr + clen]);
            done += clen;
            self.ptr += clen;
            if self.ptr == self.buf.len() {
                self.refill();
            }
        }
    }

    /// Reference `prng_get_u64` (little-endian 8-byte draw).
    pub fn get_u64(&mut self) -> u64 {
        let mut buf = [0u8; 8];
        self.get_bytes(&mut buf);
        u64::from_le_bytes(buf)
    }

    /// Reference `prng_get_u8`.
    pub fn get_u8(&mut self) -> u8 {
        let mut buf = [0u8; 1];
        self.get_bytes(&mut buf);
        buf[0]
    }
}

#[inline]
fn qround(s: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize) {
    s[a] = s[a].wrapping_add(s[b]);
    s[d] ^= s[a];
    s[d] = s[d].rotate_left(16);
    s[c] = s[c].wrapping_add(s[d]);
    s[b] ^= s[c];
    s[b] = s[b].rotate_left(12);
    s[a] = s[a].wrapping_add(s[b]);
    s[d] ^= s[a];
    s[d] = s[d].rotate_left(8);
    s[c] = s[c].wrapping_add(s[d]);
    s[b] ^= s[c];
    s[b] = s[b].rotate_left(7);
}
