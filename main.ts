// A tiny stack VM for make.fun's "Build a tiny stack virtual machine" bounty.
// One program runs every drawn bytecode program and answers with exactly the bytes
// it wrote and the exit code it ended with. The machine is ISA.md's, in its order:
// 32-bit values that wrap, a 256-value data stack, 64 return addresses, 256 words
// of memory, input bytes, at most 65,536 output bytes and 1,000,000 steps, and ten
// traps with their own exit codes. The hard rules are all here: Math.imul for MUL,
// the -2147483648 / -1 and % -1 cases, unsigned DIVU/MODU/LTU, shifts masked to
// the low 5 bits, PUSH8's sign extension, EXIT's low byte, and every trap's code
// with the output written before it kept.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Opcode byte: [immediate bytes, pops, pushes].
const OPS: Record<number, [number, number, number]> = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x10: [0, 2, 1], 0x11: [0, 2, 1], 0x12: [0, 2, 1], 0x13: [0, 2, 1],
  0x14: [0, 2, 1], 0x15: [0, 2, 1], 0x16: [0, 2, 1], 0x17: [0, 1, 1],
  0x18: [0, 2, 1], 0x19: [0, 2, 1], 0x1a: [0, 2, 1], 0x1b: [0, 1, 1],
  0x1c: [0, 2, 1], 0x1d: [0, 2, 1], 0x1e: [0, 2, 1], 0x20: [0, 2, 1],
  0x21: [0, 2, 1], 0x22: [0, 2, 1], 0x30: [2, 0, 0], 0x31: [2, 1, 0],
  0x32: [2, 1, 0], 0x33: [2, 0, 0], 0x34: [0, 0, 0], 0x40: [0, 1, 1],
  0x41: [0, 2, 0], 0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1],
  0x53: [0, 1, 0],
};

/** Runs one program on its input: the bytes it wrote and the exit code it ended with. */
function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const done = (code: number): { out: Uint8Array; code: number } => ({ out: out.slice(0, olen), code });
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= p.length) return done(9);
    const op = OPS[p[pc]!]!;
    if (op === undefined) return done(5);
    const [imm, pops, pushes] = op;
    if (pc + imm >= p.length) return done(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return done(2);
    if (sp - pops + pushes > 256) return done(3);
    pc = next;
    switch (p[pc - 1 - imm]!) {
      case 0x00: return done(0);
      case 0x01: D[sp++] = (p[next - 1]! << 24) >> 24; break;
      case 0x02: D[sp++] = p[next - 4]! | (p[next - 3]! << 8) | (p[next - 2]! << 16) | (p[next - 1]! << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]!; sp++; break;
      case 0x05: { const t = D[sp - 1]!; D[sp - 1] = D[sp - 2]!; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]!; sp++; break;
      case 0x07: { const a = D[sp - 3]!; D[sp - 3] = D[sp - 2]!; D[sp - 2] = D[sp - 1]!; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1]! | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]!; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1]!;
        const a = D[sp - 2]!;
        const oc = p[pc - 1 - imm]!;
        let r: number;
        if (oc === 0x10) r = (a + b) | 0;
        else if (oc === 0x11) r = (a - b) | 0;
        else if (oc === 0x12) r = Math.imul(a, b);
        else if (oc === 0x13) { if (b === 0) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (oc === 0x14) { if (b === 0) return done(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (oc === 0x15) { if (b === 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (oc === 0x16) { if (b === 0) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (oc === 0x18) r = a & b;
        else if (oc === 0x19) r = a | b;
        else if (oc === 0x1a) r = a ^ b;
        else if (oc === 0x1c) r = a << (b & 31);
        else if (oc === 0x1d) r = a >> (b & 31);
        else if (oc === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (oc === 0x20) r = a === b ? 1 : 0;
        else if (oc === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[next - 2]! | (p[next - 1]! << 8)) << 16) >> 16;
        const oc = p[pc - 1 - imm]!;
        let take = true;
        if (oc !== 0x30) {
          const v = D[--sp]!;
          take = oc === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return done(7);
        C[cp++] = next;
        pc = p[next - 2]! | (p[next - 1]! << 8);
        break;
      case 0x34:
        if (cp === 0) return done(8);
        pc = C[--cp]!;
        break;
      case 0x40: {
        const addr = D[sp - 1]!;
        if (addr < 0 || addr >= 256) return done(6);
        D[sp - 1] = M[addr]!;
        break;
      }
      case 0x41: {
        const addr = D[sp - 1]!;
        const v = D[sp - 2]!;
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]!);
        if (olen + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return done(11);
        out[olen++] = D[--sp]! & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++]! : -1; break;
      case 0x53: return done(D[--sp]! & 255);
    }
  }
}

for (const id of readdirSync(I).sort()) {
  const { out, code } = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
