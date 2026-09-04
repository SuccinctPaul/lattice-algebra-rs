import { defineConfig } from 'vocs/config'

export default defineConfig({
  title: 'Lattice Algebra RS',
  titleTemplate: '%s · Lattice Algebra RS',
  description:
    '统一的格密码代数基座：一套 algebra 基础库，直上 NIST PQC 方案（ML-KEM / ML-DSA / Falcon）与 lattice-based zkSNARK。',
  sidebar: [
    { text: '总览', link: '/' },
    {
      text: '入门',
      items: [
        { text: '快速开始', link: '/introduction/getting-started' },
        { text: '现状审计与差距分析', link: '/introduction/audit' },
      ],
    },
    {
      text: '架构设计',
      items: [
        { text: '分层架构总览', link: '/design/architecture' },
        { text: 'L0 · 标量环', link: '/design/scalar-ring' },
        { text: 'L1 · NTT 引擎', link: '/design/ntt' },
        { text: 'L2 · 多项式与商环', link: '/design/polynomial-ring' },
        { text: 'L3 · 模格层', link: '/design/module-lattice' },
        { text: 'L4 · 采样层', link: '/design/sampling' },
        { text: 'L4 · 哈希与 Fiat–Shamir', link: '/design/hash-fiat-shamir' },
        { text: 'L4 · 序列化', link: '/design/serialization' },
      ],
    },
    {
      text: '上层方案',
      items: [
        { text: 'NIST PQC 映射', link: '/schemes/pqc' },
        { text: 'Lattice ZK 与 zkSNARK', link: '/schemes/zk-snark' },
      ],
    },
    {
      text: '参考',
      items: [
        { text: 'Trait 地图', link: '/reference/trait-map' },
        { text: '参数集', link: '/reference/parameter-sets' },
        { text: '生态对比', link: '/reference/ecosystem' },
      ],
    },
    { text: '路线图', link: '/roadmap' },
  ],
})
