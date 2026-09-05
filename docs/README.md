# Design Docs (VOCs)

This directory hosts the project documentation site built with [Vocs](https://vocs.dev): **design = usage = reference** documentation in English, with native Mermaid diagram support.

## Local development

```bash
cd docs
npm install
npm run dev        # dev server (hot reload) — served under /lattice-algebra-rs
npm run build      # full static build (HTML emitted to dist/public)
npm run preview    # preview the built site
```

The site is deployed to **https://succinctpaul.github.io/lattice-algebra-rs/** by CI on every push to `main` (`.github/workflows/ci.yml`, `docs-deploy` job). The `basePath` in `vocs.config.ts` must stay in sync with the repository name.

## Layout

```text
docs/
├── vocs.config.ts        # site config (title, sidebar)
├── src/pages/            # all pages (MDX); file path = URL
│   ├── index.mdx             # vision & positioning
│   ├── introduction/         # quickstart, audit & gap analysis
│   ├── design/               # architecture, module map, L0–L4 designs
│   ├── schemes/              # PQC mapping, lattice ZK / zkSNARK roadmap
│   ├── reference/            # trait map, parameter sets, ecosystem
│   └── roadmap.mdx           # milestones & acceptance criteria
└── package.json
```

## Writing conventions

- Diagrams use ` ```mermaid ` fenced blocks (rendered natively by vocs).
- Code examples are labeled "current API" or "design target"; "current API" snippets must match real signatures in `src/` and are exercised by doc tests where possible.
- Public traits/modules ship their doc-page updates in the same PR (`reference/trait-map` and `design/module-map` are PR-template checkboxes).
- Parameter changes must update `reference/parameter-sets`; SNARK parameter changes additionally require an archived lattice-estimator run.

## Version note

`waku` is pinned to `1.0.0-beta.6`: vocs 2.8.5's `ScrollRestoration` relies on the waku-beta `unstable_events` router API, which changed in `1.0.0-rc.0` (symptom: SSR HTML renders, then the client hydrates to a blank page with `Cannot read properties of undefined (reading 'on')`). Re-check this pin when upgrading vocs.
