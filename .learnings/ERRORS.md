# Errors

Command failures and integration errors.

---

## [ERR-20250612-001] glob_tool_false_negative

**Logged**: 2026-06-12T00:30:00+08:00
**Priority**: critical
**Status**: resolved
**Area**: infra

### Summary
Glob tool returned "No files found" for an existing file (AGENT.md), causing false assumption that file didn't exist, leading to Write overwrite.

### Error

```
Glob pattern: D:/OpenClaw/leanprove/AGENT.md
Result: No files found
Reality: file existed with 34 rules
```

### Context
- Tool: Glob
- Input: exact absolute path with no wildcard
- Environment: Windows/Git Bash

### Suggested Fix
Replace Glob tool with `find`, `ls`, or `test -f`. Glob is now permanently banned.

### Metadata
- Reproducible: unknown
- Related Files: AGENT.md
- See Also: LRN-20250612-002

---
