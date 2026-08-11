<pre>
smartstrace v1.6.9
=====================================

USAGE:
  smartstrace [options] [strace flags]

SCRIPT FLAGS:
-------------------------------------
  --alert-cpu        Print a live alert when a traced process has CPU% above N
  --alert-errors     Print a live alert when any PID's error count exceeds N
  --auto-profile     Detect running services and auto-select relevant profiles
  --change-log       Show version history
  --context          Number of strace lines to capture as context around each error (default: 3)
  --context-only     Print strace context blocks directly in terminal output under each PID section; no log flags required
  --csf              Check CSF firewall status and correlate with traced connection errors
  --exclude-profile  Exclude one or more profiles from the active set (comma-separated)
  --full             Show full changelog history (used with --change-log)
  --help             Display help information
  --incident-mode    Comprehensive 60-second capture: health check, all profiles, auto-logging (top 10 PIDs)
  --info             Show a guided overview of smartstrace with use-case examples for sysadmins and analysts
  --json-only        Suppress human output; print a single JSON object when tracing ends
  --json-stream      Stream one JSON line per event to stdout as tracing runs (NDJSON)
  --log              Enable structured logging to /var/log/smartstrace-logs/YYYY/MM/DD/HH/
  --min-errors       Only show PIDs with at least N total errors in terminal output (log always gets all)
  --no-color         Disable ANSI color output (color is auto-enabled when stdout is a TTY)
  --profile          Run one or more analysis profiles (comma-separated)
  --profile-check    Check availability of each profile and exit (no tracing)
  --quick            Quick 2-second scan, top process only, brief output
  --report           Write a structured human-readable report to /var/log/smartstrace-logs/
  --run              Continuous monitoring mode (no timeout)
  --segs             Focus on segmentation fault detection; summarize SIGSEGV events
  --service          Trace processes by service name (comma-separated for multiple)
  --similar          After tracing, group PIDs with similar syscall fingerprints
  --status           System health check + short analysis across all profiles (top 5 PIDs)
  --sum-logs         Recursively scan a directory and produce a structured summary of strace output.
  Accepts smartstrace log files (named <mode>.<user>.<pid>.<timestamp>) and raw
  strace output files (e.g. from strace -ff -o prefix). Format is auto-detected
  from file content. Output sections: RUN COMPARISON, PROCESS ANALYSIS SUMMARY,
  CROSS-RUN PATTERNS. Standalone flag -- cannot be combined with tracing flags.
  --top              Set max processes shown in analysis output (default: 5, or 10 for --incident-mode)
  --user             Trace processes owned by one or more users (comma-separated)
  --watch            Print a live alert when any strace line matches PATTERN (implies --run unless --quick/--incident-mode/--status is set)
  --watch-cooldown   Seconds between repeated --watch alerts for the same PID (default: 30)

PROFILES:
-------------------------------------
  cron       Cron daemon tracing  [targets: pgrep -x crond (or pgrep -x cron)]
  fpm        PHP-FPM worker tracing  [targets: pgrep -f php-fpm]
  io         Disk / file I/O tracing  [targets: top-N by CPU (filtered to file+desc syscalls)]
  mysql      MySQL tracing  [targets: pgrep -x mysqld]
  network    Network diagnostics  [targets: top-N by CPU (filtered to network syscalls)]
  nginx      Nginx worker tracing  [targets: pgrep -x nginx]
  node       Node.js process tracing  [targets: pgrep -x node]
  php        PHP application tracing  [targets: pgrep -f php]
  redis      Redis server tracing  [targets: pgrep -x redis-server]
  user       User activity tracing  [targets: top-N by CPU (all users) or pgrep -u <user> when --user is given]

STRACE FLAGS:
-------------------------------------
  -T            Show syscall duration
  -e            Trace specific syscalls (e.g. -e trace=network)
  -f            Follow processes
  -ff           Follow forks (separate output per PID)
  -o            Write output to file
  -s            String size (e.g. -s4096)
  -t            Timestamps
  -tt           High precision timestamps
  -v            Verbose output
  -vv           Very verbose output
  -y            File descriptor paths
  -yy           Extended descriptor decoding

Notes:
  Flags can be combined (e.g. -Ttt, -ff)
  Some flags require values (-e, -s, -o)

Examples:
  smartstrace --quick
  smartstrace --status
  smartstrace --status --top=10
  smartstrace --incident-mode
  smartstrace --incident-mode --top=20
  smartstrace --profile=network,php
  smartstrace --profile=all                   (all profiles)
  smartstrace --profile=all --exclude-profile=cron,redis
  smartstrace --profile=user                  (all users, grouped)
  smartstrace --profile=user --user=apache    (apache only)
  smartstrace --service=httpd,nginx
  smartstrace --service=all                   (all services)
  smartstrace --auto-profile
  smartstrace --json-only --status
  smartstrace --alert-errors=10 --alert-cpu=80 --run
  smartstrace --min-errors=5 --incident-mode
  smartstrace --context-only --quick
  smartstrace --context=5 --context-only --profile=php
  smartstrace --segs --csf --report
  smartstrace --sum-logs=/var/log/smartstrace-logs/2026/05/22

Tip: Run --info for a guided overview with scenario-based examples.
     Run --sum-logs=PATH to summarize previously captured log files.

=====================================
</pre>
