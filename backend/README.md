# backend

QCP 证明库的最小子集，只包含 `benchmarks/` 下用例编译所需的部分。
本目录是抽取结果，**不要在此直接开发**。

| | 内容 | 入库 |
|---|---|---|
| `Rocq/` | 263 个 `.v`，18 个 `-R`/`-Q` 逻辑库 | 是 |
| `Lean/` | 1145 个 `.lean`，11 个 Lake package | 是 |
| `QCP_examples/` | 68 个 `.strategies`/`.h`，symexec 的输入侧共享定义 | 是 |
| `binary/` | 4 平台 × `symexec`、`StrategyCheck` | **否，见下** |

## 二进制单独取

`binary/` 不入库：13 MB 的平台构建，大约每周重发一次，逐版提交会让历史无限膨胀。
改为挂在 GitHub release 上：

```sh
tools/fetch-backend-binaries.sh       # macOS / Linux / Git Bash
tools\fetch-backend-binaries.ps1      # Windows PowerShell
```

脚本把归档解到 `backend/binary/`（`.sh` 版还会补上可执行位；Windows 不需要）。也可以自己下载解压，只要
`backend/binary/` 下是 `linux-binary/`、`mac-arm64-binary/`、`mac-x86-64-binary/`、
`win-binary/` 四个目录即可。

## 用法

Rocq —— `benchmarks/CONFIGURE` 默认已指向这里：

```sh
cd benchmarks
cp CONFIGURE.example CONFIGURE
make -j6
```

Lean —— 用 `-KqcpLean` 指向 `backend/Lean`：

```sh
cd benchmarks
lake -KqcpLean=../backend/Lean build
```

`backend/Lean` 的 `flocq` 与 `unifysl` 依赖 Mathlib v4.25.2，Lake 首次构建会从 git
拉取（约 650 MB，落在 `benchmarks/.lake/packages/`）。**拉完先跑一次
`lake exe cache get`** 取预编译 olean，否则会从源码编译 Mathlib，耗时数小时。
