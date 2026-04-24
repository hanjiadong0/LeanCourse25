# AI-tool

`AI-tool` is the Lean-first AI hub for this repository.

It keeps the ownership order clear:

- `LeanCourse25` is the main working repo
- `AI-tool` is the reusable tool and bridge layer
- `Science-Work-Flow-` is treated as an external evaluation framework
- `OpenGauss` is treated as an external Lean workflow tool

## Goals

- keep Lean development centered in this repo
- make OpenGauss easy to launch against this Lean project
- keep evaluation tooling connected without making the evaluation repo the dependency root
- provide a thesis-writing workspace that can later point to a real thesis repo
- make future projects easy to add through one local config file

## Layout

- `config/`
  - `profiles.example.json` documents the profile schema
  - `profiles.local.json` is your machine-local configuration and is ignored by git
- `external/`
  - local junction-style links to tools such as OpenGauss
- `evaluations/`
  - local links to evaluation frameworks such as `Science-Work-Flow-`
- `projects/`
  - local links to Lean repos or future target repos
- `scripts/`
  - common helpers, link sync, doctor, OpenGauss launcher, thesis starter
- `workspaces/thesis/`
  - prompts and notes for thesis writing

## First Run

From the repo root:

```powershell
powershell -ExecutionPolicy Bypass -File .\LeanCourse25\AI-tool\scripts\Sync-AIToolLinks.ps1
cmd /c .\LeanCourse25\AI-tool\scripts\AITool-Doctor.cmd
cmd /c .\LeanCourse25\AI-tool\scripts\OpenGauss-Project.cmd doctor
```

## OpenGauss Workflow

```powershell
cmd /c .\LeanCourse25\AI-tool\scripts\OpenGauss-Project.cmd
```

That launches the configured OpenGauss runner inside the configured Lean project profile.

## Thesis Workflow

```powershell
cmd /c .\LeanCourse25\AI-tool\scripts\Start-Thesis-Workspace.cmd
```

If you later create a dedicated thesis repo, set its path in `config\profiles.local.json` and rerun `Sync-AIToolLinks.ps1`.
