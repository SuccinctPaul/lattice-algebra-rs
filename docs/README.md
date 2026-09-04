# 设计文档站（VOCs）

本目录是基于 [Vocs](https://vocs.dev) 的项目文档站，承载**架构设计 / 使用文档 / 参考文档**三位一体的内容，原生支持 Mermaid 图表。

## 本地开发

```bash
cd docs
npm install
npm run dev        # 开发服务器（热更新）
npm run build      # 产出 dist/（SSR + 静态资源）
npm run preview    # 本地预览构建产物
```

## 结构

```text
docs/
├── vocs.config.ts        # 站点配置（标题、侧边栏）
├── src/pages/            # 所有页面（MDX），路径即 URL
│   ├── index.mdx             # 愿景与定位
│   ├── introduction/         # 快速开始、现状审计
│   ├── design/               # L0–L4 分层设计（架构核心）
│   ├── schemes/              # PQC 映射、lattice ZK/zkSNARK 路线
│   ├── reference/            # trait 地图、参数集、生态对比
│   └── roadmap.mdx           # 里程碑与验收标准
└── package.json
```

## 写作约定

- 图表一律使用 ` ```mermaid ` 代码块（vocs 内置渲染）；
- 代码示例标注「当前 API」或「设计目标 API」；「当前 API」示例须与 `src/` 真实签名一致；
- 修改公共 trait / 新增模块时，**同一天内**更新对应设计页与 `reference/trait-map`（PR 模板勾选项）；
- 参数变更必须同步 `reference/parameter-sets`，SNARK 参数需附 lattice-estimator 运行记录。

## 版本注意

`waku` 依赖被钉在 `1.0.0-beta.6`：vocs 2.8.5 的 `ScrollRestoration` 依赖 waku beta 的 `unstable_events` 路由 API，`1.0.0-rc.0` 起该 API 变更会导致白屏（症状：页面 SSR HTML 正常但客户端水合后 DOM 清空，报 `Cannot read properties of undefined (reading 'on')`）。升级 vocs 时同步复核该 pin。
