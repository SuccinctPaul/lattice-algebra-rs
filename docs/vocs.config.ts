import { defineConfig } from 'vocs/config'

export default defineConfig({
  // Serves the site under the GitHub Pages project path
  // (https://<user>.github.io/lattice-algebra-rs).
  basePath: '/lattice-algebra-rs',
  // Prerender every page to static HTML so the `dist` output can be hosted
  // on GitHub Pages (the default 'dynamic' strategy emits a Node server).
  renderStrategy: 'full-static',
  title: 'Lattice Algebra RS',
  titleTemplate: '%s · Lattice Algebra RS',
  description:
    'A unified lattice-cryptography algebra foundation: one base library from which NIST PQC schemes (ML-KEM / ML-DSA / Falcon) and lattice-based zkSNARKs derive directly.',
  sidebar: [
    { text: 'Overview', link: '/' },
    {
      text: 'Getting Started',
      items: [
        { text: 'Prerequisites & Notation', link: '/introduction/prerequisites' },
        { text: 'Quickstart', link: '/introduction/getting-started' },
        { text: 'Integration Guide', link: '/introduction/integrating' },
        { text: 'Security Status', link: '/introduction/security-status' },
        { text: 'Audit & Gap Analysis', link: '/introduction/audit' },
      ],
    },
    {
      text: 'Design',
      items: [
        { text: 'Architecture', link: '/design/architecture' },
        { text: 'Module Map', link: '/design/module-map' },
        { text: 'L0 · Scalar Rings', link: '/design/scalar-ring' },
        { text: 'L1 · NTT Engine', link: '/design/ntt' },
        { text: 'L2 · Polynomials', link: '/design/polynomial-ring' },
        { text: 'L3 · Module Lattices', link: '/design/module-lattice' },
        { text: 'L4 · Sampling', link: '/design/sampling' },
        { text: 'L4 · Hashing & Fiat–Shamir', link: '/design/hash-fiat-shamir' },
        { text: 'L4 · Serialization', link: '/design/serialization' },
      ],
    },
    {
      text: 'Schemes',
      items: [
        { text: 'NIST PQC Mapping', link: '/schemes/pqc' },
        { text: 'Lattice ZK & zkSNARK', link: '/schemes/zk-snark' },
        { text: 'Z1 · Ajtai & Σ-Protocols', link: '/schemes/z1-sigma' },
        { text: 'Z2 · Batched Openings', link: '/schemes/z2-batched' },
        { text: 'Z3 · Ring-Sumcheck & IPA', link: '/schemes/z3-sumcheck' },
      ],
    },
    {
      text: 'Reference',
      items: [
        { text: 'Trait Map', link: '/reference/trait-map' },
        { text: 'Parameter Sets', link: '/reference/parameter-sets' },
        { text: 'Performance', link: '/reference/performance' },
        { text: 'Ecosystem', link: '/reference/ecosystem' },
      ],
    },
    { text: 'Roadmap', link: '/roadmap' },
  ],
})
