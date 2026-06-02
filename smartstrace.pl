#!/usr/bin/perl
use strict;
use warnings;
use Getopt::Long;
use POSIX qw(strftime mktime);
use File::Find qw(find);

my $VERSION = "1.6.9";

my %MONTHS = qw(Jan 0 Feb 1 Mar 2 Apr 3 May 4 Jun 5 Jul 6 Aug 7 Sep 8 Oct 9 Nov 10 Dec 11);

# =============================================
# COLOR SUPPORT
# ANSI codes; only active when stdout is a TTY
# and --no-color is not set.
# =============================================
my $USE_COLOR = 0;  # set after flag parsing (--no-color not parsed yet here)

sub _c {
 my ($code, $text) = @_;
 return $USE_COLOR ? "\e[${code}m${text}\e[0m" : $text;
}
sub c_red    { _c("31",   $_[0]) }
sub c_yellow { _c("33",   $_[0]) }
sub c_green  { _c("32",   $_[0]) }
sub c_bold   { _c("1",    $_[0]) }
sub c_cyan   { _c("36",   $_[0]) }


# =============================================
# GLOBAL RUNTIME DATA
# Declared early so all named subs below can
# close over these lexicals regardless of where
# the subs appear in the file.
# =============================================
my %pid_errors;
my %syscall_count;
my %pid_context;   # rolling 3-line buffer per PID for error context capture
my %pid_cpu;       # CPU% observed for each PID at selection time
my %pid_mem;       # Memory % observed for each PID at selection time
my %pid_rss;       # RSS (KB) observed for each PID at selection time
my %pid_etimes;    # Elapsed seconds since process start, captured at selection time
my $total_traced  = 0;
my $total_errors  = 0;
my $log_written   = 0;
my ($log_dir, $log_file);
my $status_mode   = 0;
my @target_pids;
my %alerted_errors;
my %alerted_cpu;
my @profiles;
my @strace_extra;
my @profile_strace_args;
my $ptrace_denied    = 0;   # count of PIDs strace could not attach to
my $d_state_skipped  = 0;   # count of PIDs skipped because they were in D state
my %pid_source_profiles;    # $pid_source_profiles{$pid}{$profile} = 1 for each profile that targeted the PID
my %pid_rss_initial;        # RSS at first sample per PID (KB)
my %pid_rss_peak;           # Highest RSS seen per PID (KB)
my $last_rss_sample;        # Time of last periodic RSS sample
my $trace_start_time;       # Set on first main loop iteration
my $trace_end_time;         # Set at start of finish()
my $watch_pattern;          # Compiled regex for --watch mode
my %watch_last_alert;       # Last alert time per PID for --watch cooldown
my $strace_timeout;         # Per-PID strace timeout (set in main execution block)
my %watch_match_count;      # Match count per PID for --watch tally
my $service_summary_shown = 0;  # Track if SERVICE TRACE SUMMARY has been printed
my $web_stack;              # Cached result of detect_web_stack()
my %profile_pid_count;      # Count of PIDs found per profile in get_profile_targets
my %health_summary;         # WARNING/CRITICAL findings from server_health check


# -----------------------------
# FLAGS
# -----------------------------
my @raw_argv = @ARGV;

my ($run,$status,$quick,$json_only,$json_stream,$help,$change_log,$full);
my ($profile,$profile_check,$auto_profile,$incident_mode);
my ($segs,$csf,$similar);
my ($top_n,$cpu_threshold,$user,$pid_filter);
my ($alert_errors,$alert_cpu,$report,$service,$log);
my ($watch,$watch_cooldown);
my ($min_errors,$no_color,$exclude_profile);
my ($context_n,$context_only);
my $info;
my $sum_logs;

# top_n intentionally left undef here so the context-sensitive default
# in the NORMALIZE section can set 5 (general/status) or 10 (incident-mode).
# --top=N on the command line will set it via GetOptions, which takes precedence.
$cpu_threshold = 50;

Getopt::Long::Configure("pass_through","bundling");

GetOptions(
 "run"            => \$run,
 "status"         => \$status,
 "quick"          => \$quick,
 "json-only"      => \$json_only,
 "json-stream"    => \$json_stream,
 "profile:s"      => \$profile,
 "profile-check"  => \$profile_check,
 "auto-profile"   => \$auto_profile,
 "incident-mode"  => \$incident_mode,
 "segs"           => \$segs,
 "csf"            => \$csf,
 "similar"        => \$similar,
 "top=i"          => \$top_n,
 "cpu=i"          => \$cpu_threshold,
 "user=s"         => \$user,
 "pid=s"          => \$pid_filter,
 "alert-errors=i" => \$alert_errors,
 "alert-cpu=i"    => \$alert_cpu,
 "report"         => \$report,
 "service=s"      => \$service,
 "log"            => \$log,
 "change-log"       => \$change_log,
 "full"             => \$full,
 "help|h"           => \$help,
 "watch=s"          => \$watch,
 "watch-cooldown=i" => \$watch_cooldown,
 "min-errors=i"      => \$min_errors,
 "no-color"          => \$no_color,
 "exclude-profile=s" => \$exclude_profile,
 "context=i"         => \$context_n,
 "context-only"      => \$context_only,
 "info"              => \$info,
 "sum-logs=s"        => \$sum_logs,
);

# -----------------------------
# FLAG NORMALIZATION
# -----------------------------

# detect help anywhere (handles malformed inputs)
for my $arg (@raw_argv) {
 if ($arg =~ /--help/ || $arg eq "-h") {
  $help = 1;
 }
}

# fix --user swallowing another flag
if (defined $user && $user =~ /^--/) {
 if ($user eq "--help" || $user eq "-h") {
  $help = 1;
  $user = undef;
 } else {
  print "\nInvalid value for --user: $user\n\n";
  exit 1;
 }
}

# --top without a value (bare --top or --top=) -- print usage and exit cleanly
if (!defined $top_n && grep { /^--top$|^--top=$/ } @raw_argv) {
 print "\n--top requires a numeric value\n\n";
 print "Examples:\n";
 print "  smartstrace --top=5\n";
 print "  smartstrace --status --top=10\n";
 print "  smartstrace --incident-mode --top=20\n\n";
 exit 1;
}

# fix --service swallowing another flag
if (defined $service && $service =~ /^--/) {
 if ($service eq "--help" || $service eq "-h") {
  $help = 1;
  $service = undef;
 } else {
  print "\nInvalid value for --service: $service\n\n";
  exit 1;
 }
}

# --service=all: expand to the full supported service list.
# Note: @supported_services is declared after flag parsing; we handle this
# expansion after that declaration (see "service=all expansion" below).

# normalize profile string
if (defined $profile) {
 $profile =~ s/\s+//g;
 $profile = "" if $profile eq "";
}

# --color: enable after flag parsing so --no-color is respected.
# Only active when stdout is a TTY.
$USE_COLOR = (-t STDOUT && !$no_color) ? 1 : 0;

# --watch flag normalization
if (defined $watch) {
 # Imply --run only when no explicit timing flag is set.
 # --quick, --incident-mode, and --status all carry their own timeouts;
 # --watch should respect them rather than forcing infinite mode.
 $run = 1 unless $quick || $incident_mode || $status;
 $watch_cooldown //= 30;
 $watch_pattern = eval { qr/$watch/i };
 if ($@) {
  print "\nInvalid --watch pattern: $@\n\n";
  exit 1;
 }
}


# -----------------------------
# INVALID SHORT FLAG DETECTION
# -----------------------------
for my $arg (@raw_argv) {

 if ($arg =~ /^-([^-].*)$/) {
  my $body = $1;

  if ($body =~ /^[A-Za-z0-9]+$/) {
   next;
  }

  if ($body =~ /^[eos]$/) {
   next;
  }

  print "\nInvalid flag format: $arg\n";
  print "Use -- for long flags (e.g. --profile, --help)\n\n";
  exit 1;
 }
}


# -----------------------------
# HELP DATA
# -----------------------------

my @supported_services = qw(
 httpd nginx lshttpd ea-nginx mysqld mariadbd
 exim dovecot cpsrvd cpaneld webmaild whostmgrd
 redis crond node
);

# service=all expansion (requires @supported_services to exist)
if (defined $service && lc($service) eq 'all') {
 $service = join(",", @supported_services);
}

my %script_flag_help = (

 run => {
  desc    => "Continuous monitoring mode (no timeout)",
  example => "smartstrace --run",
 },

 status => {
  desc    => "System health check + short analysis across all profiles (top 5 PIDs)",
  example => "smartstrace --status",
 },

 quick => {
  desc    => "Quick 2-second scan, top process only, brief output",
  example => "smartstrace --quick",
 },

 "json-only" => {
  desc    => "Suppress human output; print a single JSON object when tracing ends",
  example => "smartstrace --json-only",
 },

 "json-stream" => {
  desc    => "Stream one JSON line per event to stdout as tracing runs (NDJSON)",
  example => "smartstrace --json-stream",
 },

 service => {
  desc    => "Trace processes by service name (comma-separated for multiple)",
  example => "smartstrace --service=httpd,nginx",
 },

 user => {
  desc    => "Trace processes owned by one or more users (comma-separated)",
  example => "smartstrace --user=root,apache",
 },

 profile => {
  desc    => "Run one or more analysis profiles (comma-separated)",
  values  => "network | php | io | mysql | user | fpm | nginx | redis | node | cron",
  example => "smartstrace --profile=network,io",
 },

 "profile-check" => {
  desc    => "Check availability of each profile and exit (no tracing)",
  example => "smartstrace --profile-check",
 },

 "auto-profile" => {
  desc    => "Detect running services and auto-select relevant profiles",
  example => "smartstrace --auto-profile",
 },

 "incident-mode" => {
  desc    => "Comprehensive 60-second capture: health check, all profiles, auto-logging (top 10 PIDs)",
  example => "smartstrace --incident-mode",
 },

 segs => {
  desc    => "Focus on segmentation fault detection; summarize SIGSEGV events",
  example => "smartstrace --segs",
 },

 csf => {
  desc    => "Check CSF firewall status and correlate with traced connection errors",
  example => "smartstrace --csf",
 },

 similar => {
  desc    => "After tracing, group PIDs with similar syscall fingerprints",
  example => "smartstrace --similar",
 },

 report => {
  desc    => "Write a structured human-readable report to /var/log/smartstrace-logs/",
  example => "smartstrace --report",
 },

 top => {
  desc    => "Set max processes shown in analysis output (default: 5, or 10 for --incident-mode)",
  example => "smartstrace --top=10",
 },

 "alert-errors" => {
  desc    => "Print a live alert when any PID's error count exceeds N",
  example => "smartstrace --alert-errors=10",
 },

 "alert-cpu" => {
  desc    => "Print a live alert when a traced process has CPU% above N",
  example => "smartstrace --alert-cpu=80",
 },

 log => {
  desc    => "Enable structured logging to /var/log/smartstrace-logs/YYYY/MM/DD/HH/",
  example => "smartstrace --log",
 },

 "change-log" => {
  desc    => "Show version history",
  example => "smartstrace --change-log --full",
 },

 full => {
  desc => "Show full changelog history (used with --change-log)",
 },

 help => {
  desc => "Display help information",
 },

 watch => {
  desc    => "Print a live alert when any strace line matches PATTERN (implies --run unless --quick/--incident-mode/--status is set)",
  example => "smartstrace --watch='ECONNREFUSED.*3306'",
 },

 "watch-cooldown" => {
  desc    => "Seconds between repeated --watch alerts for the same PID (default: 30)",
  example => "smartstrace --watch='ENOENT' --watch-cooldown=10",
 },

 "min-errors" => {
  desc    => "Only show PIDs with at least N total errors in terminal output (log always gets all)",
  example => "smartstrace --min-errors=10 --incident-mode",
 },

 "no-color" => {
  desc    => "Disable ANSI color output (color is auto-enabled when stdout is a TTY)",
  example => "smartstrace --no-color --status",
 },

 "exclude-profile" => {
  desc    => "Exclude one or more profiles from the active set (comma-separated)",
  example => "smartstrace --profile=all --exclude-profile=cron,redis",
 },

 "context" => {
  desc    => "Number of strace lines to capture as context around each error (default: 3)",
  example => "smartstrace --context=5 --log",
 },

 "context-only" => {
  desc    => "Print strace context blocks directly in terminal output under each PID section; no log flags required",
  example => "smartstrace --context-only --context=5 --quick",
 },

 "info" => {
  desc    => "Show a guided overview of smartstrace with use-case examples for sysadmins and analysts",
  example => "smartstrace --info",
 },

 "sum-logs" => {
  desc    => "Recursively scan a directory and produce a structured summary of strace output.\n" .
             "  Accepts smartstrace log files (named <mode>.<user>.<pid>.<timestamp>) and raw\n" .
             "  strace output files (e.g. from strace -ff -o prefix). Format is auto-detected\n" .
             "  from file content. Output sections: RUN COMPARISON, PROCESS ANALYSIS SUMMARY,\n" .
             "  CROSS-RUN PATTERNS. Standalone flag -- cannot be combined with tracing flags.",
  example => "smartstrace --sum-logs=/var/log/smartstrace-logs/2026/05/22",
 },
);

my %profile_help = (

 network => {
  desc      => "Network diagnostics",
  behavior  => "Targets top-CPU processes; traces network syscalls only",
  focus     => "Connections, traffic, ECONNREFUSED, ETIMEDOUT",
  processes => "top-N by CPU (filtered to network syscalls)",
  example   => "smartstrace --profile=network",
 },

 php => {
  desc      => "PHP application tracing",
  behavior  => "Targets running PHP processes via pgrep",
  focus     => "File access, missing includes, permission errors",
  processes => "pgrep -f php",
  example   => "smartstrace --profile=php",
 },

 io => {
  desc      => "Disk / file I/O tracing",
  behavior  => "Targets top-CPU processes; traces file/descriptor syscalls",
  focus     => "Read/write activity, open/close patterns, ENOENT",
  processes => "top-N by CPU (filtered to file+desc syscalls)",
  example   => "smartstrace --profile=io",
 },

 mysql => {
  desc      => "MySQL tracing",
  behavior  => "Targets mysqld process(es) via pgrep",
  focus     => "Network connections, IPC, query-related errors",
  processes => "pgrep -x mysqld",
  example   => "smartstrace --profile=mysql",
 },

 user => {
  desc      => "User activity tracing",
  behavior  => "Without --user: traces top-N processes across all users, grouped by user. With --user: filters to processes owned by the specified user(s) only.",
  focus     => "User-owned processes, permission errors",
  processes => "top-N by CPU (all users) or pgrep -u <user> when --user is given",
  example   => "smartstrace --profile=user",
 },

 fpm => {
  desc      => "PHP-FPM worker tracing",
  behavior  => "Targets php-fpm worker processes via pgrep",
  focus     => "File access, network, process errors in FPM workers",
  processes => "pgrep -f php-fpm",
  example   => "smartstrace --profile=fpm",
 },

 nginx => {
  desc      => "Nginx worker tracing",
  behavior  => "Targets nginx worker processes via pgrep",
  focus     => "Network connections, file access",
  processes => "pgrep -x nginx",
  example   => "smartstrace --profile=nginx",
 },

 redis => {
  desc      => "Redis server tracing",
  behavior  => "Targets redis-server process(es) via pgrep",
  focus     => "Network connections, IPC",
  processes => "pgrep -x redis-server",
  example   => "smartstrace --profile=redis",
 },

 node => {
  desc      => "Node.js process tracing",
  behavior  => "Targets node process(es) via pgrep",
  focus     => "Network connections, file access",
  processes => "pgrep -x node",
  example   => "smartstrace --profile=node",
 },

 cron => {
  desc      => "Cron daemon tracing",
  behavior  => "Targets crond process(es) via pgrep",
  focus     => "All syscalls (no filter) -- cron job activity",
  processes => "pgrep -x crond (or pgrep -x cron)",
  example   => "smartstrace --profile=cron",
 },
);

my %strace_flag_help = (
 "T"  => "Show syscall duration",
 "t"  => "Timestamps",
 "tt" => "High precision timestamps",
 "f"  => "Follow processes",
 "ff" => "Follow forks (separate output per PID)",
 "y"  => "File descriptor paths",
 "yy" => "Extended descriptor decoding",
 "v"  => "Verbose output",
 "vv" => "Very verbose output",
 "s"  => "String size (e.g. -s4096)",
 "e"  => "Trace specific syscalls (e.g. -e trace=network)",
 "o"  => "Write output to file",
);

my %strace_flag_notes = (
 combined => "Flags can be combined (e.g. -Ttt, -ff)",
 values   => "Some flags require values (-e, -s, -o)",
);

my %error_causes = (
 ENOENT        => "Missing file or directory",
 EACCES        => "Permission denied",
 ETIMEDOUT     => "Operation timed out",
 ECONNREFUSED  => "Connection refused",
 SIGSEGV       => "Segmentation fault (possible crash)",
 EMFILE        => "Too many open files (file descriptor limit hit)",
 ENOSPC        => "No space left on device",
 EADDRINUSE    => "Address already in use (port conflict)",
);

# Path patterns -> (short description, actionable detail) for ENOENT/EACCES hints.
# Matched in order; first match wins.
my @path_hints = (
 [ qr{mysql\.sock|mysqld\.sock}i,       "MySQL socket missing",
   "systemctl status mysqld  (or: service mysqld status)" ],
 [ qr{pgsql|postgres.*\.sock}i,         "PostgreSQL socket missing",
   "systemctl status postgresql" ],
 [ qr{redis\.sock}i,                    "Redis socket missing",
   "systemctl status redis" ],
 [ qr{php.*fpm.*\.sock|fpm.*\.sock|php.*\.sock}i, "PHP-FPM socket missing",
   "systemctl status php-fpm  (or: ps aux | grep php-fpm)" ],
 [ qr{memcache.*\.sock}i,               "Memcached socket missing",
   "systemctl status memcached" ],
 [ qr{/etc/ssl|\.pem$|\.crt$|\.key$}i, "SSL certificate or key file missing",
   "ls -la <path>  -- cert may need to be generated or renewed" ],
 [ qr{/etc/php|php\.ini|php\.d/}i,      "PHP configuration file missing",
   "php --ini  -- check expected config path" ],
 [ qr{/etc/resolv\.conf}i,              "DNS resolver config missing",
   "cat /etc/resolv.conf  -- may need to recreate" ],
 [ qr{/etc/localtime}i,                 "Timezone data file missing",
   "ln -sf /usr/share/zoneinfo/UTC /etc/localtime" ],
 [ qr{\.htaccess}i,                     "Apache .htaccess file missing",
   "check directory permissions and AllowOverride setting" ],
 [ qr{/var/run/}i,                      "Runtime socket or PID file missing -- service may have crashed",
   "ls /var/run/  and restart the relevant service" ],
 [ qr{/tmp/}i,                          "Temporary file missing -- possible race condition or cleared /tmp",
   "df -h /tmp  -- check if /tmp is full or was recently cleared" ],
 [ qr{/proc/\d+/}i,                     "Process already exited before syscall completed (transient)",
   "(no action needed -- process exit race)" ],
);

# Port number -> [service name, actionable check command]
my %port_hints = (
 3306  => ["MySQL",        "ss -tlnp | grep 3306  ||  systemctl status mysqld"],
 5432  => ["PostgreSQL",   "ss -tlnp | grep 5432  ||  systemctl status postgresql"],
 6379  => ["Redis",        "ss -tlnp | grep 6379  ||  systemctl status redis"],
 11211 => ["Memcached",    "ss -tlnp | grep 11211 ||  systemctl status memcached"],
 9200  => ["Elasticsearch","ss -tlnp | grep 9200  ||  systemctl status elasticsearch"],
 27017 => ["MongoDB",      "ss -tlnp | grep 27017 ||  systemctl status mongod"],
 80    => ["HTTP server",  "ss -tlnp | grep ':80 ' ||  systemctl status httpd nginx"],
 443   => ["HTTPS server", "ss -tlnp | grep ':443'"],
 8080  => ["HTTP (alt)",   "ss -tlnp | grep 8080"],
 2082  => ["cPanel",       "whmapi1 servicestatus service=cpanel  ||  systemctl status cpanel"],
 2083  => ["cPanel SSL",   "whmapi1 servicestatus service=cpanel"],
 2086  => ["WHM",          "whmapi1 servicestatus service=whostmgrd"],
 2087  => ["WHM SSL",      "whmapi1 servicestatus service=whostmgrd"],
 21    => ["FTP server",   "ss -tlnp | grep ':21 ' ||  systemctl status vsftpd proftpd"],
 22    => ["SSH",          "ss -tlnp | grep ':22 '"],
 25    => ["SMTP",         "ss -tlnp | grep ':25 '  ||  systemctl status postfix exim"],
 53    => ["DNS server",   "ss -tlnp | grep ':53 ' ||  systemctl status named bind9"],
);

my %changelog = (

 "1.6.9" => [
  "--sum-logs=PATH: recursively scans a directory and produces a structured summary",
  "  of strace output without running a new trace. Accepts two file formats:",
  "    smartstrace logs  -- identified by filename <mode>.<user>.<pid>.<timestamp>",
  "    raw strace output -- auto-detected from content (supports strace -ff, -tt, -f)",
  "  Files from 'strace -ff -o prefix' are grouped by common prefix + mtime bucket",
  "  so all prefix.PID files from one invocation appear as a single run.",
  "  Output sections:",
  "    RUN COMPARISON     -- all runs, newest-first (mode shows 'raw-strace' for plain",
  "                          strace files; user shows '(unknown)' when not available)",
  "    PROCESS ANALYSIS SUMMARY -- per-PID error breakdown with extracted paths and",
  "                          addresses; confidence scored from error volume",
  "    CROSS-RUN PATTERNS -- error+target pairs recurring across 2+ runs; persistent",
  "                          PIDs across runs",
  "  Standalone flag -- cannot be combined with operational tracing flags.",
  "  Uses File::Find for recursive scan; parse_raw_strace_file() handles raw format.",
  "  Error extraction from raw strace: ENOENT/EACCES/ENOSPC paths from quoted args;",
  "    ECONNREFUSED/ETIMEDOUT/EADDRINUSE addresses from sin_addr/sin_port or sun_path.",
 ],

 "1.6.8" => [
  "--context=N: configures the rolling strace context buffer depth per PID.",
  "  Default is 3 lines. Affects both terminal context-only output and log blocks.",
  "",
  "--context-only: prints captured strace context blocks to terminal output under",
  "  each PID's section in PROCESS ANALYSIS (user / service / default grouping).",
  "  No log flags required. Error lines are highlighted (prefixed with '>' and",
  "  colored red when ANSI color is active). Blocks are capped at 10 unique",
  "  occurrences per error type per PID (same as log).",
  "  Can be combined with --context=N to widen the capture window.",
  "",
  "show_pid_context_terminal(\$pid, \$indent) added; called in all three PROCESS",
  "  ANALYSIS display paths when --context-only is set.",
  "",
  "--info: prints a guided overview of smartstrace with scenario-based examples",
  "  for sysadmins and analysts -- quick workflows, flag combinations, and",
  "  recommendations for common diagnostic situations.",
 ],

 "1.6.7" => [
  "New error types tracked: EMFILE (too many open files), ENOSPC (no space left),",
  "  EADDRINUSE (port conflict). All three have actionable hints in terminal and log output.",
  "  ENOSPC also extracts the path argument; EADDRINUSE extracts the address.",
  "",
  "--min-errors=N: suppress PIDs with fewer than N total errors from terminal display.",
  "  Log always records all PIDs regardless of this setting.",
  "",
  "--no-color: disable ANSI color output.",
  "  Color is auto-enabled when stdout is a TTY, suppressed otherwise (pipes, logs, etc.).",
  "  Color applied to: CRITICAL (red), WARNING (yellow), ACTIVE (green), NOT RUNNING (red).",
  "",
  "--exclude-profile=PROFILE[,...]: remove named profiles from the active set.",
  "  Useful with --profile=all or --incident-mode to skip irrelevant profiles.",
  "",
  "--profile=all: expand to all known profiles (same set as --status / --incident-mode).",
  "--service=all: expand to all supported services.",
  "",
  "--pid now accepts comma-separated values (--pid=1234,5678) to trace multiple specific PIDs.",
  "",
  "--auto-profile log filename changed from 'multi-profile' to 'auto-profile'.",
  "",
  "cron profile: tightened fallback from pgrep -f cron (too broad) to pgrep -x cron.",
  "  Prevents matching unrelated processes that have 'cron' anywhere in their arguments.",
  "",
  "Color support added via c_red(), c_yellow(), c_green(), c_bold(), c_cyan() helpers.",
  "  USE_COLOR set at startup: active when -t STDOUT and --no-color not passed.",
  "  All Unicode output characters replaced with ASCII: em dash -> --, arrow -> ->",
  "  Timeline bar character changed from UTF-8 block to '#' for universal terminal compat.",
 ],

 "1.6.6" => [
  "binmode(STDOUT, ':utf8') added to fix Wide character warnings from █ in timeline.",
  "",
  "Timeline label format fixed: label built as full string first, then padded to 12 chars.",
  "  Bucket size calculation uses ceiling division: int((\$duration + 19) / 20).",
  "",
  "correlate_logs() now also requires total_errors > 0 and total_traced > 0 before running.",
  "",
  "--watch and --watch-cooldown now have contextual help entries in the help system.",
  "",
  "SERVICE TRACE SUMMARY printed once before tracing when --service is used.",
  "  Shows each service's running state, PIDs (up to 5), and count to trace.",
  "",
  "SERVICE ERROR BREAKDOWN added to finish() when \$service is defined and errors found.",
  "  Groups error PIDs by matching service name; unmatched PIDs go under 'other'.",
  "",
  "Health Alert echoed in GLOBAL SUMMARY when --status or --incident-mode is active.",
  "  Populated from %health_summary filled by check_system_health().",
  "",
  "WATCH SUMMARY added to finish() when --watch matched at least one line.",
  "  Shows pattern, PIDs sorted by match count descending.",
  "  %watch_match_count tracks per-PID match count in the strace loop.",
  "",
  "CSF BLOCK CORRELATION: check_csf() now parses /etc/csf/csf.deny and cross-references",
  "  extracted ECONNREFUSED/ETIMEDOUT addresses against the deny list.",
  "",
  "--incident-mode SERVICE STATUS now shows process count per service.",
  "",
  "--pid end-of-trace existence check: if /proc/\$pid_filter gone, NOTE shown in summary.",
  "",
  "detect_web_stack() helper added; result cached in \$web_stack global.",
  "  Used for stack-aware php profile discovery (lsphp + php-fpm) and LiteSpeed log.",
  "",
  "Profile discovery updated:",
  "  php: additive -- lsphp (LiteSpeed), php-fpm workers, fallback pgrep -f php.",
  "  mysql: also checks mariadbd as fallback.",
  "  New profiles: fpm, nginx, redis, node, cron.",
  "",
  "get_profile_strace_args() updated for fpm, nginx, redis, node profiles.",
  "  cron uses no filter (all syscalls, like user).",
  "",
  "New profiles added to %profile_help: fpm, nginx, redis, node, cron.",
  "",
  "\@supported_services updated to include: lshttpd, ea-nginx, mariadbd, redis, crond, node.",
  "",
  "LiteSpeed error.log added to correlate_logs() log sources (only when lshttpd running).",
  "",
  "Profile zero-result reporting: PROFILE SUMMARY shows profiles that found 0 processes.",
  "  %profile_pid_count tracks per-profile discovery count in get_profile_targets().",
  "",
  "Profile active syscall filter shown in PROFILE SUMMARY header for each profile.",
 ],

 "1.6.5" => [
  "Error Timeline: show_error_timeline() renders an ASCII bar chart of errors across time",
  "  Buckets all %pid_errors timestamps into at most 20 slots relative to trace start.",
  "  Displayed in finish() after PROCESS ANALYSIS, only when total_errors > 0.",
  "  Header: ERROR TIMELINE; each row shows time range, bar (█ chars), and count.",
  "",
  "RSS Growth Tracking: periodic re-sampling of RSS for all known PIDs every 15 seconds.",
  "  %pid_rss_initial and %pid_rss_peak track first and highest RSS values seen.",
  "  show_rss_growth() flags PIDs where growth >= 20% AND >= 5 MB.",
  "  Displayed as MEMORY GROWTH section in finish() before GLOBAL SUMMARY.",
  "",
  "Process Tree Awareness: get_parent_chain() reads /proc/PID/status to walk up to 4 levels.",
  "  show_process_tree() formats 'Parent chain: name (PID N) -> ...' via say_out.",
  "  Called in all three PROCESS ANALYSIS display blocks after process_stats_annotation.",
  "",
  "Syscall Hotspot Reporting: show_syscall_hotspots() shows top 5 syscalls per PID.",
  "  Printed as 'Syscalls :' with count and rate per second (count/duration).",
  "  Called in all three PROCESS ANALYSIS display blocks after show_process_tree.",
  "",
  "cPanel/WHM Log Correlation: correlate_logs() scans known cPanel log files.",
  "  Only runs when /usr/local/cpanel or /opt/cpanel exists.",
  "  Tails last 500 lines of each log, filters entries within trace window (±5s buffer).",
  "  parse_log_timestamp() handles Apache/cPanel, syslog, and ISO timestamp formats.",
  "  Displays LOG CORRELATION section in finish() after show_rss_growth.",
  "  Capped at 50 total entries; skips notice/info/debug lines to reduce noise.",
  "",
  "--watch=PATTERN mode: print live alert when any strace line matches the given regex.",
  "  Implies --run unless --quick/--incident-mode/--status is also set (those retain their timeout).",
  "  Respects --watch-cooldown=N seconds between repeated alerts per PID (default 30).",
  "  Alert format: [WATCH] PID N (cmd)  matched_line",
  "",
  "Fixed PROFILE SUMMARY showing incorrect process attribution:",
  "  Previously guessed profile membership from error types (ENOENT -> io+php,",
  "  ECONNREFUSED -> network+mysql).  Now uses %pid_source_profiles populated at",
  "  discovery time -- a PID only appears under a profile if that profile targeted it.",
  "",
  "Fixed missing use POSIX qw(strftime mktime) import that caused exit 255 on any",
  "  run that reached per-PID output (introduced in v1.6.4).",
 ],

 "1.6.4" => [
  "Extended per-PID process stats in terminal and log output:",
  "  CPU usage   -- already captured; now displayed consistently in all three display paths",
  "  Memory      -- %MEM and RSS (auto-scaled to KB/MB/GB) captured at selection time",
  "  Started     -- process start timestamp derived from elapsed seconds (etimes field)",
  "  Running for -- human-readable uptime: Xd Xh Xm Xs",
  "",
  "  Terminal output (PROCESS ANALYSIS) shows all four fields under each PID header.",
  "  Log output (ERROR DETAIL) includes the same fields before the per-error breakdown.",
  "  High-CPU annotation ([HIGH] flag and investigation commands) retained.",
  "",
  "  ps -eo command extended to pid,ppid,%cpu,%mem,rss,etimes in all three selection",
  "  loops (default, network/io profile, user all-users).  --pid mode captures stats",
  "  from ps -p at the time the process name is read from /proc/<pid>/comm.",
  "",
  "  format_elapsed() helper converts seconds to Xd Xh Xm Xs for display.",
 ],

 "1.6.3" => [
  "Default strace string size set to -s256:",
  "  strace truncates path strings to 32 chars by default, making ENOENT paths unreadable.",
  "  256 chars covers virtually all real-world paths without producing buffer-content noise",
  "  from read()/write() calls.  Overridden if user passes their own -s flag.",
  "",
  "Path extraction for ENOENT and EACCES:",
  "  The path argument is parsed from openat/stat/access/unlink/rename/chmod/etc. lines.",
  "  Top paths by occurrence count shown under each error type in both terminal and log.",
  "  Pattern library maps common paths to specific actionable hints:",
  "    MySQL/PostgreSQL/Redis/PHP-FPM sockets, SSL certs, /var/run/ runtime files, etc.",
  "",
  "Address and port extraction for ECONNREFUSED and ETIMEDOUT:",
  "  connect() destination (IP:port or Unix socket path) parsed from strace output.",
  "  Top destinations shown under each error type.",
  "  Port-to-service mapping provides specific next-step commands for known ports.",
  "",
  "Burst detection:",
  "  Timestamps recorded per error occurrence.  When 5+ errors occur within 1 second,",
  "  the error line is annotated with [BURST: N in 1s] to distinguish transient spikes",
  "  from persistent steady-state failures.",
  "",
  "Cross-PID shared failure correlation:",
  "  After tracing, paths and addresses seen in 2+ PIDs are collected into a",
  "  SHARED FAILURES section in both terminal and log output.  Surfaces systemic",
  "  problems (a service is down) vs. isolated per-process issues.",
  "",
  "Recommendations now path- and port-aware:",
  "  Generic recommendations replaced with specific actionable advice derived from",
  "  extracted paths and ports wherever a known pattern matches.",
 ],

 "1.6.2" => [
  "D-state process detection: processes in uninterruptible sleep are skipped before tracing",
  "  Attaching to a D-state process via ptrace is not possible -- the process cannot receive",
  "  SIGSTOP or deliver ptrace events while blocked in the kernel.  Worse, if the process",
  "  transitions to D state after attachment, strace's PTRACE_DETACH call can itself block,",
  "  leaving the strace child and its parent timeout process permanently stuck.",
  "  Detection reads /proc/<pid>/status State: field.  A [SKIP] line is printed per process.",
  "  D-state skip count shown in GLOBAL SUMMARY alongside ptrace_denied count.",
  "",
  "timeout --kill-after=3 added to strace invocation:",
  "  After the per-PID strace timeout, SIGTERM is sent to strace.  If strace has entered",
  "  D state trying to PTRACE_DETACH, it will not respond to SIGTERM.  --kill-after=3 ensures",
  "  SIGKILL is sent 3 seconds later, preventing zombie strace processes.",
  "",
  "ptrace denial message now includes targeted, environment-aware hints:",
  "  Reads /proc/sys/kernel/yama/ptrace_scope to determine whether lowering scope would help",
  "  Detects SELinux enforcing mode and suggests: ausearch -m avc -ts recent | grep ptrace",
  "  Detects AppArmor active profiles",
  "  Detects CloudLinux and explains that protected system processes cannot be traced even as root",
  "  When ptrace_scope is already 0, explicitly states that another policy is blocking ptrace",
  "  Applies to both terminal output (GLOBAL SUMMARY) and log file",
 ],

 "1.6.1" => [
  "System health metrics added to --status and --incident-mode",
  "  Reads load average from /proc/loadavg, memory from /proc/meminfo, I/O wait from iostat",
  "  Reports WARNING when metrics are elevated, CRITICAL when truly problematic",
  "  Thresholds: load WARNING > num_cpus, CRITICAL > num_cpus x 2",
  "              memory WARNING > 80%, CRITICAL > 95%",
  "              I/O wait WARNING > 20%, CRITICAL > 50%",
  "  --status reports CRITICAL metrics and suggests --incident-mode when warranted",
  "",
  "--incident-mode overhauled (fully self-contained comprehensive analysis):",
  "  Sections: server health, profile status, service status, user status, process analysis",
  "  Default top 10 PIDs (overridable with --top=N)",
  "  Extended error context for high-error PIDs written to log only (not terminal)",
  "  SAR availability noted if found",
  "",
  "--top flag default is now context-sensitive:",
  "  Default 10 for --incident-mode, 5 for --status and general use",
  "  --top=N always overrides the default",
  "",
  "Log path format changed:",
  "  New: /var/log/smartstrace-logs/YYYY/MM/DD/HH/\$service.\$user.\$pid.\$timestamp",
  "  Service: --service value, profile name(s) joined, or 'default'",
  "  User: --user value, process owner lookup, or 'unknown'",
  "  PID: single PID or 'multi' for multiple processes",
  "",
  "Service validation enhanced:",
  "  --service now verifies each named service is actually running after name check",
  "  Warning printed if service is not found; tracing proceeds so PIDs can be re-checked",
  "",
  "Summary grouping and top-N limiting in process analysis:",
  "  Process analysis limited to top-N PIDs sorted by error count (highest first)",
  "  Groups by user when --profile=user or --user is specified",
  "  Groups by service when --service is specified",
  "  Shows UID next to each PID in default grouping",
  "  Truncation note shown when more PIDs exist than the display limit",
  "",
  "--profile=user no longer requires --user:",
  "  Without --user: traces top-N processes across ALL users, grouped by user in output",
  "  With --user=<name>: narrows to only those user(s) -- --user is now an optional filter",
  "",
  "Help system updated: --status, --incident-mode, --top, --log, --report, --profile=user",
 ],

 "1.6.0" => [
  "MAJOR RELEASE -- comprehensive rewrite of core engine and all flag implementations",
  "",
  "New flags (fully implemented):",
  "  --quick: 2-second fast scan mode (top process only, brief output)",
  "  --json-only: suppress human output; emit a single JSON blob at end of run",
  "  --json-stream: stream one NDJSON line per event to stdout as tracing runs",
  "  --profile-check: verify profile availability and exit without tracing",
  "  --auto-profile: detect running services and auto-select relevant profiles",
  "  --incident-mode: run all profiles for 60 seconds with auto-logging",
  "  --segs: segfault focus mode with dmesg cross-reference",
  "  --csf: CSF firewall status check and connection-error correlation",
  "  --similar: group traced PIDs by overlapping syscall fingerprints",
  "  --report: write a structured human-readable report to /var/log/smartstrace/",
  "  --alert-errors=N: live alert when any PID error count exceeds N",
  "  --alert-cpu=N: live alert when a traced process CPU% exceeds N",
  "",
  "Profile improvements:",
  "  Fixed profile-specific process targeting (php/mysql now use pgrep, not top-CPU fallback)",
  "  Fixed profile-specific strace syscall filters (network=-e network, io=-e file,desc, etc.)",
  "  Added validation: --profile=user warns and skips when --user is not specified",
  "  Combined profiles now merge their syscall filter groups correctly",
  "",
  "Bug fixes:",
  "  Fixed strace stderr leaking to terminal (fork-based open with STDERR->STDOUT redirect)",
  "  Fixed script running indefinitely without --run (per-PID timeout guard added)",
  "  Fixed output gating: PROCESS ANALYSIS and PROFILE SUMMARY suppressed when no errors found",
  "  Fixed process analysis listing all PIDs instead of only errored ones",
  "  Fixed --log not writing full structured output including error context",
  "  Fixed per-PID 'Operation not permitted' spam -- consolidated into single global NOTE",
  "  Fixed autovivification bugs causing 'Use of uninitialized value' warnings in summaries",
  "  Fixed --quick and --run conflict: --run now takes precedence with an explicit warning",
  "  Fixed version sort: numeric comparison replaces string cmp (1.5.10 now sorts after 1.5.9)",
  "  Fixed Levenshtein sub using \$a/\$b locals that shadowed Perl sort variables",
  "  Fixed --csf flag being misparsed as strace flags -c -s -f by the help system",
  "  Fixed ECONNREFUSED tracking confirmed active across all profiles and flags",
  "",
  "Help system:",
  "  Updated for all new flags and profiles",
  "  Added --quick/--run mutual-exclusion note",
  "  Added profile strace filter documentation",
  "  Added script_long_flags guard to prevent --flag names being parsed as strace args",
 ],

 "1.5.9" => [
  "Rebuilt help system (fully context-aware)",
  "Fixed flag normalization issues (--user/--service swallowing flags)",
  "Added strict runtime strace flag validation (fail-fast on invalid flags)",
  "Enhanced strace help output (detected flags + full reference always shown)",
  "Added strace flag notes (combined flags, value flags)",
  "Improved malformed flag handling (--TTtvvff normalization)",
  "Resolved timeout blocking behavior in strace execution",
  "Stabilized main loop and exit handling",
 ],

 "1.5.8" => [
  "Introduced --service targeting",
  "Improved CLI flag parsing structure",
  "Initial expansion of help system framework",
  "Improved strace flag detection logic",
 ],

 "1.5.7" => [
  "Added invalid flag highlighting",
  "Improved syscall error grouping",
  "Enhanced error tracking per PID",
 ],

 "1.5.6" => [
  "Added full changelog support (--full)",
  "Improved changelog formatting and grouping",
 ],

 "1.5.5" => [
  "Introduced confidence scoring system",
  "Added per-process error weighting",
 ],

 "1.5.4" => [
  "Introduced contextual help system foundation",
  "Added dynamic help triggers based on flags",
 ],

 "1.5.3" => [
  "Added native strace execution engine",
  "Introduced syscall tracking framework",
 ],

 "1.5.2" => [
  "Improved CLI parsing stability",
  "Fixed edge cases with flag combinations",
 ],

 "1.5.1" => [
  "Added report generation system",
  "Implemented summary output formatting",
 ],

 "1.5.0" => [
  "Introduced alerts and JSON-style output capabilities",
  "Initial structured output support",
 ],
);

my %legacy_changelog = (

 "1.4.x" => [
  "1.4.0   - Introduced profiles",
  "1.4.1   - Added profile-check system",
  "1.4.2   - Added auto-profile detection",
  "1.4.3   - Introduced initial help system",
 ],

 "1.3.x" => [
  "1.3.0   - Added segmentation fault detection",
  "1.3.1   - Added CSF suggestion integration",
  "1.3.2   - Integrated sys-snap data",
  "1.3.3   - Overhauled logging system",
 ],

 "1.2.x" => [
  "1.2.0   - Introduced structured flag system",
  "1.2.1   - Added preview/raw output mode",
  "1.2.2   - Added intelligent suggestions",
  "1.2.3   - Added root cause detection improvements",
 ],

 "1.1.x" => [
  "1.1.0   - Added dependency validation",
  "1.1.1   - Added install prompts",
  "1.1.2   - Introduced initial logging framework",
 ],

 "1.0.x" => [
  "1.0.0   - Initial strace wrapper implementation",
  "1.0.1   - Added CPU-based process filtering",
  "1.0.2   - Introduced basic error aggregation",
 ],
);


# =============================================
# SUPPORT FUNCTIONS
# =============================================

# FIX #1: version-aware sort comparator.
# The original cmp (string) sort would mis-order 1.5.10 before 1.5.9.
sub ver_cmp {
 my @av = split /\./, $a;
 my @bv = split /\./, $b;
 $bv[0] <=> $av[0] || $bv[1] <=> $av[1] || $bv[2] <=> $av[2];
}

# FIX #4: renamed $a/$b to $str1/$str2 to avoid shadowing
# Perl's magic sort variables when called from inside a sort block.
sub levenshtein {
 my ($str1, $str2) = @_;
 my @A = split //, $str1;
 my @B = split //, $str2;
 my @d;
 $d[$_][0] = $_ for 0..@A;
 $d[0][$_] = $_ for 0..@B;
 for my $i (1..@A) {
  for my $j (1..@B) {
   my $cost = ($A[$i-1] eq $B[$j-1]) ? 0 : 1;
   $d[$i][$j] = min(
    $d[$i-1][$j] + 1,
    $d[$i][$j-1] + 1,
    $d[$i-1][$j-1] + $cost
   );
  }
 }
 return $d[@A][@B];
}

sub min {
 my ($x, $y, $z) = @_;
 my $m = $x < $y ? $x : $y;
 return $z < $m ? $z : $m;
}

# FIX #7: parse_flags moved before first call site in the help system.
sub parse_flags {
 my ($arg) = @_;
 my @parsed;
 return @parsed unless $arg =~ /^-([A-Za-z]+)/;
 my $flags = $1;
 while ($flags) {
  if    ($flags =~ s/^(tt)//) { push @parsed, ["tt", undef, 1]; }
  elsif ($flags =~ s/^(ff)//) { push @parsed, ["ff", undef, 1]; }
  elsif ($flags =~ s/^(vv)//) { push @parsed, ["vv", undef, 1]; }
  elsif ($flags =~ s/^(yy)//) { push @parsed, ["yy", undef, 1]; }
  else {
   my $f = substr($flags, 0, 1, "");
   push @parsed, [$f, undef, exists $strace_flag_help{$f} ? 1 : 0];
  }
 }
 return @parsed;
}

sub calc_confidence {
 my ($errors) = @_;
 return 0 unless $errors;
 return int(100 * (1 - exp(-$errors / 10)));
}

# Compact single-line JSON value encoder (for streaming).
sub _json_scalar {
 my ($v) = @_;
 return "null"  unless defined $v;
 return $v      if $v =~ /^-?\d+$/;
 $v =~ s/\\/\\\\/g;
 $v =~ s/"/\\"/g;
 $v =~ s/\n/\\n/g;
 $v =~ s/\r/\\r/g;
 $v =~ s/\t/\\t/g;
 return "\"$v\"";
}

# Recursive pretty JSON encoder (for --json-only final blob).
sub to_json {
 my ($val, $depth) = @_;
 $depth //= 0;
 my $pad   = "  " x $depth;
 my $inner = "  " x ($depth + 1);

 if (!defined $val) { return "null" }

 if (ref $val eq 'HASH') {
  return "{}" unless %$val;
  my @pairs = map {
   my $k = $_;
   (my $ek = $k) =~ s/"/\\"/g;
   "$inner\"$ek\": " . to_json($val->{$_}, $depth + 1)
  } sort keys %$val;
  return "{\n" . join(",\n", @pairs) . "\n$pad}";
 }

 if (ref $val eq 'ARRAY') {
  return "[]" unless @$val;
  my @items = map { "$inner" . to_json($_, $depth + 1) } @$val;
  return "[\n" . join(",\n", @items) . "\n$pad]";
 }

 return _json_scalar($val);
}

# Emit a compact JSON line to stdout (--json-stream).
sub json_event {
 my ($event) = @_;
 return unless $json_stream;
 $event->{ts} = time();
 my @pairs = map { "\"$_\":" . _json_scalar($event->{$_}) } sort keys %$event;
 print "{" . join(",", @pairs) . "}\n";
}

# Emit a string to stdout, suppressed when --json-only is active.
sub say_out {
 return if $json_only;
 print @_;
}


# =============================================
# PROFILE HELPER FUNCTIONS
# =============================================

# detect_web_stack(): returns a hashref of active web stack components.
# Called lazily via: $web_stack //= detect_web_stack()
sub detect_web_stack {
 my %stack;
 # LiteSpeed
 $stack{litespeed} = 1 if `pgrep -x lshttpd 2>/dev/null` =~ /\d/;
 # Apache (check both ea-apache24 process name and httpd)
 $stack{apache} = 1 if `pgrep -x httpd 2>/dev/null` =~ /\d/
                     || `pgrep -f ea-apache24 2>/dev/null` =~ /\d/;
 # EA-Nginx
 $stack{nginx} = 1 if `pgrep -x nginx 2>/dev/null` =~ /\d/;
 # PHP-FPM (any variant including ea-phpXX-php-fpm)
 $stack{phpfpm} = 1 if `pgrep -f php-fpm 2>/dev/null` =~ /\d/;
 # lsphp (LiteSpeed PHP handler)
 $stack{lsphp} = 1 if `pgrep -f lsphp 2>/dev/null` =~ /\d/;
 # MySQL/MariaDB
 $stack{mysql} = 1 if `pgrep -x mysqld 2>/dev/null` =~ /\d/
                   || `pgrep -x mariadbd 2>/dev/null` =~ /\d/;
 # Redis
 $stack{redis} = 1 if `pgrep -x redis-server 2>/dev/null` =~ /\d/;
 # Node
 $stack{node} = 1 if `pgrep -x node 2>/dev/null` =~ /\d/;
 return \%stack;
}

# Returns the list of PIDs to trace for the given profiles.
# Each profile type has its own process discovery strategy:
#   php    -> pgrep -f php
#   mysql  -> pgrep -x mysqld (with pgrep -f fallback)
#   user   -> pgrep -u <users from --user flag>
#   network/io -> top-N by CPU (respects $top_n and $cpu_threshold)
sub get_profile_targets {
 my @profs = @_;
 my @pids;
 my %seen;

 for my $p (@profs) {
  my @found;

  if ($p eq 'php') {
   my $stack = $web_stack //= detect_web_stack();
   # lsphp under LiteSpeed
   if ($stack->{lsphp}) {
    my @lsphp = `pgrep -f lsphp 2>/dev/null`; chomp @lsphp;
    push @found, @lsphp;
   }
   # php-fpm workers (all ea-phpXX-php-fpm variants + generic)
   if ($stack->{phpfpm}) {
    my @fpm = `pgrep -f php-fpm 2>/dev/null`; chomp @fpm;
    push @found, @fpm;
   }
   # fallback: any php process
   unless (@found) {
    @found = `pgrep -f php 2>/dev/null`; chomp @found;
   }
  }
  elsif ($p eq 'fpm') {
   my @fpm = `pgrep -f php-fpm 2>/dev/null`; chomp @fpm;
   push @found, @fpm;
  }
  elsif ($p eq 'nginx') {
   my @ng = `pgrep -x nginx 2>/dev/null`; chomp @ng;
   push @found, @ng;
  }
  elsif ($p eq 'redis') {
   my @r = `pgrep -x redis-server 2>/dev/null`; chomp @r;
   push @found, @r;
  }
  elsif ($p eq 'node') {
   my @n = `pgrep -x node 2>/dev/null`; chomp @n;
   push @found, @n;
  }
  elsif ($p eq 'cron') {
   my @c = `pgrep -x crond 2>/dev/null`; chomp @c;
   unless (@c) {
    @c = `pgrep -x cron 2>/dev/null`; chomp @c;
   }
   push @found, @c;
  }
  elsif ($p eq 'mysql') {
   @found = `pgrep -x mysqld 2>/dev/null`;
   chomp @found;
   unless (@found) {
    @found = `pgrep -x mariadbd 2>/dev/null`;
    chomp @found;
   }
   unless (@found) {
    @found = `pgrep -f mysqld 2>/dev/null`;
    chomp @found;
   }
  }
  elsif ($p eq 'network' || $p eq 'io') {
   my $limit = $top_n + 1;
   my @rows = `ps -eo pid,ppid,%cpu,%mem,rss,etimes --sort=-%cpu 2>/dev/null | head -$limit`;
   shift @rows;
   chomp @rows;
   for my $row (@rows) {
    $row =~ s/^\s+//;
    my ($pid, $ppid, $cpu, $mem, $rss, $etimes) = split /\s+/, $row;
    next unless defined $pid && $pid =~ /^\d+$/;
    next if $pid == $$ || (defined $ppid && $ppid == $$);
    $pid_cpu{$pid}    = $cpu    + 0 if defined $cpu;
    $pid_mem{$pid}    = $mem    + 0 if defined $mem;
    $pid_rss{$pid}    = $rss    + 0 if defined $rss;
    $pid_etimes{$pid} = $etimes + 0 if defined $etimes;
    push @found, $pid;
   }
  }
  elsif ($p eq 'user') {
   if ($user) {
    # --user specified: target only those user(s)
    for my $u (split /,/, $user) {
     my @u_found = `pgrep -u $u 2>/dev/null`;
     chomp @u_found;
     push @found, @u_found;
    }
   } else {
    # No --user: trace top-N processes across ALL users (grouped by user in output)
    my $limit = $top_n + 1;
    my @rows  = `ps -eo pid,ppid,%cpu,%mem,rss,etimes --sort=-%cpu 2>/dev/null | head -$limit`;
    shift @rows;
    chomp @rows;
    for my $row (@rows) {
     $row =~ s/^\s+//;
     my ($pid, $ppid, $cpu, $mem, $rss, $etimes) = split /\s+/, $row;
     next unless defined $pid && $pid =~ /^\d+$/;
     next if $pid == $$ || (defined $ppid && $ppid == $$);
     $pid_cpu{$pid}    = $cpu    + 0 if defined $cpu;
     $pid_mem{$pid}    = $mem    + 0 if defined $mem;
     $pid_rss{$pid}    = $rss    + 0 if defined $rss;
     $pid_etimes{$pid} = $etimes + 0 if defined $etimes;
     push @found, $pid;
    }
   }
  }

  # Record how many PIDs this profile found (for zero-result reporting)
  $profile_pid_count{$p} = scalar(grep { /^\d+$/ } @found);

  for my $pid (@found) {
   next unless $pid =~ /^\d+$/;
   push @pids, $pid unless $seen{$pid}++;
   $pid_source_profiles{$pid}{$p} = 1;   # record which profile discovered this PID
  }
 }

 return @pids;
}

# Returns strace -e trace=... args appropriate for the given profiles.
# Combined profiles merge their syscall groups.
# Returns empty list if the user already passed an explicit -e flag.
sub get_profile_strace_args {
 my (@profs) = @_;
 my %groups;

 for my $p (@profs) {
  if    ($p eq 'network') { $groups{network} = 1; }
  elsif ($p eq 'io')      { $groups{file} = 1; $groups{desc} = 1; }
  elsif ($p eq 'php')     { $groups{file} = 1; $groups{process} = 1; }
  elsif ($p eq 'mysql')   { $groups{network} = 1; $groups{ipc} = 1; }
  elsif ($p eq 'fpm')     { $groups{file} = 1; $groups{process} = 1; $groups{network} = 1; }
  elsif ($p eq 'nginx')   { $groups{network} = 1; $groups{file} = 1; }
  elsif ($p eq 'redis')   { $groups{network} = 1; $groups{ipc} = 1; }
  elsif ($p eq 'node')    { $groups{network} = 1; $groups{file} = 1; }
  # 'user' and 'cron' profiles apply no syscall filter -- trace everything
 }

 return () unless %groups;
 return ("-e", "trace=" . join(",", sort keys %groups));
}


# =============================================
# ANALYSIS FUNCTIONS
# =============================================

# --profile-check: verify each profile's required processes/tools exist.
sub check_profiles {
 my @check = @_ ? @_ : sort keys %profile_help;

 print "\nPROFILE CHECK\n";
 print "=====================================\n\n";

 for my $p (@check) {

  my $info = $profile_help{$p} or next;
  printf "[%s]  %s\n", $p, $info->{desc};
  print  "  Targets: $info->{processes}\n";

  if ($p eq 'php') {
   my @procs = `pgrep -f php 2>/dev/null`;
   chomp @procs;
   if (@procs) {
    printf "  Status:  ACTIVE (%d PHP process(es) running)\n", scalar @procs;
   } else {
    print  "  Status:  " . c_red("NOT RUNNING") . "\n";
   }
  }
  elsif ($p eq 'mysql') {
   my @procs = `pgrep -x mysqld 2>/dev/null`;
   chomp @procs;
   unless (@procs) {
    @procs = `pgrep -x mariadbd 2>/dev/null`;
    chomp @procs;
   }
   if (@procs) {
    print "  Status:  " . c_green("ACTIVE") . " (mysqld/mariadbd running)\n";
   } else {
    print "  Status:  NOT RUNNING\n";
   }
  }
  elsif ($p eq 'fpm') {
   my @procs = `pgrep -f php-fpm 2>/dev/null`;
   chomp @procs;
   if (@procs) {
    printf "  Status:  ACTIVE (%d php-fpm process(es) running)\n", scalar @procs;
   } else {
    print  "  Status:  " . c_red("NOT RUNNING") . "\n";
   }
  }
  elsif ($p eq 'nginx') {
   my @procs = `pgrep -x nginx 2>/dev/null`;
   chomp @procs;
   if (@procs) {
    printf "  Status:  ACTIVE (%d nginx process(es) running)\n", scalar @procs;
   } else {
    print  "  Status:  " . c_red("NOT RUNNING") . "\n";
   }
  }
  elsif ($p eq 'redis') {
   my @procs = `pgrep -x redis-server 2>/dev/null`;
   chomp @procs;
   if (@procs) {
    print "  Status:  " . c_green("ACTIVE") . " (redis-server running)\n";
   } else {
    print "  Status:  NOT RUNNING\n";
   }
  }
  elsif ($p eq 'node') {
   my @procs = `pgrep -x node 2>/dev/null`;
   chomp @procs;
   if (@procs) {
    printf "  Status:  ACTIVE (%d node process(es) running)\n", scalar @procs;
   } else {
    print  "  Status:  " . c_red("NOT RUNNING") . "\n";
   }
  }
  elsif ($p eq 'cron') {
   my @procs = `pgrep -x crond 2>/dev/null`;
   chomp @procs;
   unless (@procs) {
    @procs = `pgrep -x cron 2>/dev/null`; chomp @procs;
   }
   if (@procs) {
    printf "  Status:  ACTIVE (%d cron process(es) running)\n", scalar @procs;
   } else {
    print  "  Status:  " . c_red("NOT RUNNING") . "\n";
   }
  }
  elsif ($p eq 'network') {
   my $ss = `which ss 2>/dev/null`;
   chomp $ss;
   my $tool = $ss ? $ss : "basic syscall tracing";
   print "  Status:  AVAILABLE (using $tool)\n";
  }
  elsif ($p eq 'io') {
   print "  Status:  AVAILABLE\n";
  }
  elsif ($p eq 'user') {
   if ($user) {
    my @found;
    for my $u (split /,/, $user) {
     my @u_found = `pgrep -u $u 2>/dev/null`;
     chomp @u_found;
     push @found, @u_found;
    }
    if (@found) {
     printf "  Status:  ACTIVE (%d process(es) for user(s): %s)\n",
            scalar @found, $user;
    } else {
     print "  Status:  NO PROCESSES (none found for: $user)\n";
    }
   } else {
    printf "  Status:  AVAILABLE (will trace top-%d processes across all users)\n", $top_n;
    print  "  Note:    Use --user=<name> to limit to specific user(s)\n";
   }
  }

  print "\n";
 }
}

# --auto-profile: detect which profiles make sense given what's running.
sub detect_auto_profiles {
 my @detected;

 say_out "\nAuto-detecting profiles...\n";

 my @php = `pgrep -f php 2>/dev/null`;
 chomp @php;
 if (@php) {
  push @detected, 'php';
  say_out sprintf("  Detected: php (%d process(es))\n", scalar @php);
 }

 my @mysql = `pgrep -x mysqld 2>/dev/null`;
 chomp @mysql;
 unless (@mysql) {
  @mysql = `pgrep -x mariadbd 2>/dev/null`;
  chomp @mysql;
 }
 if (@mysql) {
  push @detected, 'mysql';
  say_out "  Detected: mysql (mysqld/mariadbd running)\n";
 }

 my $conns = `ss -tn 2>/dev/null | grep -c ESTABLISHED` // 0;
 chomp $conns;
 if ($conns > 0) {
  push @detected, 'network';
  say_out "  Detected: network ($conns active TCP connections)\n";
 }

 push @detected, 'io';
 say_out "  Detected: io (always included)\n";

 if ($user) {
  push @detected, 'user';
  say_out "  Detected: user (--user=$user)\n";
 }

 say_out "\n";
 return @detected;
}

# --csf: check CSF status and correlate with traced connection errors.
sub check_csf {
 print "\nCSF STATUS\n";
 print "=====================================\n\n";

 my $csf_bin = `which csf 2>/dev/null`;
 chomp $csf_bin;

 unless ($csf_bin) {
  print "  CSF not installed (csf not found in PATH)\n\n";
  return;
 }

 print "  CSF binary:  $csf_bin\n";

 my $csf_status = `csf --status 2>/dev/null | head -3`;
 if ($csf_status =~ /disabled/i) {
  print "  CSF status:  DISABLED\n";
 } elsif ($csf_status) {
  print "  CSF status:  ACTIVE\n";
 } else {
  print "  CSF status:  UNKNOWN (could not query)\n";
 }

 my @lfd = `pgrep -x lfd 2>/dev/null`;
 printf "  LFD daemon:  %s\n\n", (@lfd ? c_green("RUNNING") : c_red("NOT RUNNING"));

 # Cross-reference traced connection errors with CSF
 my @blocked_pids = grep {
  my $e = $pid_errors{$_}->{errors} // {};
  (exists $e->{ECONNREFUSED} && ($e->{ECONNREFUSED}->{count} // 0) > 0) ||
  (exists $e->{ETIMEDOUT}    && ($e->{ETIMEDOUT}->{count}    // 0) > 0)
 } keys %pid_errors;

 if (@blocked_pids) {

  print "  PIDs with connection errors (possible CSF blocks):\n";

  for my $pid (sort @blocked_pids) {
   my $econn = $pid_errors{$pid}->{errors}{ECONNREFUSED}->{count} // 0;
   my $etime = $pid_errors{$pid}->{errors}{ETIMEDOUT}->{count}    // 0;
   my $cmd   = `ps -o comm= -p $pid 2>/dev/null`;
   chomp $cmd;
   printf "    PID %-7s  %-15s  ECONNREFUSED=%-4d  ETIMEDOUT=%d\n",
          $pid, ($cmd || "unknown"), $econn, $etime;
  }

  print "\n";

  if (-f "/etc/csf/csf.deny") {
   my $deny_count = `wc -l < /etc/csf/csf.deny 2>/dev/null`;
   chomp $deny_count;
   $deny_count =~ s/^\s+//;
   print "  CSF deny list: $deny_count entr" . ($deny_count == 1 ? "y" : "ies") . "\n";
   print "  Tip: run 'csf -l' to see active blocks, 'csf -g <ip>' to check a specific IP\n";
  }

 } else {
  print "  No connection errors found that would indicate CSF blocks\n";
 }

 print "\n";

 # CSF BLOCK CORRELATION
 # Parse /etc/csf/csf.deny and cross-reference traced connection error addresses
 if (-f "/etc/csf/csf.deny") {
  # Collect all addresses from pid_errors
  my %traced_addrs;
  for my $pid (keys %pid_errors) {
   for my $err (qw(ECONNREFUSED ETIMEDOUT)) {
    my $addrs = $pid_errors{$pid}->{errors}{$err}->{addrs} // {};
    for my $addr (keys %$addrs) {
     push @{$traced_addrs{$addr}}, { pid => $pid, err => $err,
                                     count => $addrs->{$addr} };
    }
   }
  }

  if (%traced_addrs) {
   # Build set of IPs in csf.deny
   my %denied_ips;
   if (open(my $df, "<", "/etc/csf/csf.deny")) {
    while (<$df>) {
     chomp;
     next if /^\s*#/ || /^\s*$/;
     if (/^\s*(\d{1,3}(?:\.\d{1,3}){3})/) {
      $denied_ips{$1} = 1;
     }
    }
    close $df;
   }

   my @correlations;
   for my $addr (sort keys %traced_addrs) {
    # Extract IP from addr like "1.2.3.4:3306" or "[::1]:80"
    my ($ip) = $addr =~ /^([^:]+):/;
    $ip //= $addr;
    $ip =~ s/^\[|\]$//g;  # strip IPv6 brackets
    if ($denied_ips{$ip}) {
     for my $info (@{$traced_addrs{$addr}}) {
      push @correlations, { addr => $addr, ip => $ip,
                            pid => $info->{pid}, err => $info->{err},
                            count => $info->{count} };
     }
    }
   }

   if (@correlations) {
    print "CSF BLOCK CORRELATION\n";
    print "-------------------------------------\n";
    for my $c (@correlations) {
     my $cmd = $pid_errors{$c->{pid}}->{cmd} // "?";
     printf "  %-25s  BLOCKED in CSF   (seen in PID %s %s x%d)\n",
            $c->{addr}, $c->{pid}, $c->{err}, $c->{count};
    }
    print "\n";
   }
  }
 }
}

# --similar: group traced PIDs by overlapping syscall fingerprints.
sub find_similar {
 print "\nSIMILAR PROCESS ANALYSIS\n";
 print "=====================================\n\n";

 my %fingerprints;

 for my $pid (keys %syscall_count) {
  my @top = sort { $syscall_count{$pid}{$b} <=> $syscall_count{$pid}{$a} }
                keys %{$syscall_count{$pid}};
  @top = @top[0..4] if @top > 5;
  $fingerprints{$pid} = \@top;
 }

 if (keys %fingerprints < 2) {
  print "  Not enough PIDs traced to compare (need at least 2)\n\n";
  return;
 }

 my @pids = keys %fingerprints;
 my %assigned;
 my @groups;

 for my $i (0..$#pids) {
  my $p1 = $pids[$i];
  next if $assigned{$p1};

  my @group = ($p1);
  $assigned{$p1} = 1;

  for my $j ($i+1..$#pids) {
   my $p2 = $pids[$j];
   next if $assigned{$p2};
   my %fp1     = map { $_ => 1 } @{$fingerprints{$p1}};
   my $overlap = grep { $fp1{$_} } @{$fingerprints{$p2}};
   if ($overlap >= 3) {
    push @group, $p2;
    $assigned{$p2} = 1;
   }
  }

  push @groups, \@group;
 }

 my $found_similar = 0;

 for my $grp (@groups) {
  next unless @$grp > 1;
  $found_similar = 1;
  printf "  Similar group (%d PIDs):\n", scalar @$grp;
  for my $pid (@$grp) {
   my $cmd       = `ps -o comm= -p $pid 2>/dev/null`;
   chomp $cmd;
   my $err_total = $pid_errors{$pid}->{total} // 0;
   printf "    PID %-7s  %-15s  errors=%-4d  top-syscalls: %s\n",
          $pid,
          ($cmd || "unknown"),
          $err_total,
          join(",", @{$fingerprints{$pid}});
  }
  print "\n";
 }

 unless ($found_similar) {
  print "  All traced PIDs have distinct syscall patterns\n\n";
 }
}

# --segs: summarize segmentation fault events and cross-check dmesg.
sub show_segs_summary {
 print "\nSEGFAULT SUMMARY\n";
 print "=====================================\n\n";

 my $found = 0;

 for my $pid (sort keys %pid_errors) {
  my $count = $pid_errors{$pid}->{errors}{SIGSEGV}->{count} // 0;
  next unless $count;
  my $cmd = `ps -o comm= -p $pid 2>/dev/null`;
  chomp $cmd;
  printf "  PID %-7s  %-15s  %d segfault(s)\n",
         $pid, ($cmd || "unknown"), $count;
  $found++;
 }

 # Cross-reference with kernel dmesg log
 my @dmesg = `dmesg 2>/dev/null | grep -i 'segfault' | tail -5`;
 if (@dmesg) {
  print "\n  Recent kernel segfaults (dmesg):\n";
  for my $line (@dmesg) {
   chomp $line;
   print "    $line\n";
  }
 }

 unless ($found || @dmesg) {
  print "  No segmentation faults detected\n";
 }

 print "\n";
}

# --report: write a structured human-readable report file.
sub write_report {
 my $timestamp  = time();
 my $report_dir = "/var/log/smartstrace";

 mkdir $report_dir unless -d $report_dir;

 my $report_file;
 if (-d $report_dir && -w $report_dir) {
  $report_file = "$report_dir/report-$timestamp.txt";
 } else {
  $report_file = "smartstrace-report-$timestamp.txt";
 }

 open(my $rf, ">", $report_file) or do {
  print "Failed to write report: $report_file\n";
  return;
 };

 my @lt = localtime($timestamp);
 my $date = sprintf "%04d-%02d-%02d %02d:%02d:%02d",
            $lt[5]+1900, $lt[4]+1, $lt[3], $lt[2], $lt[1], $lt[0];

 print $rf "===========================================\n";
 print $rf "smartstrace Report\n";
 print $rf "Version  : $VERSION\n";
 print $rf "Generated: $date\n";
 print $rf "Profiles : " . (@profiles ? join(", ", @profiles) : "none") . "\n";
 print $rf "===========================================\n\n";

 # System overview
 my $uptime = `uptime 2>/dev/null`;
 chomp $uptime;
 print $rf "SYSTEM OVERVIEW\n";
 print $rf "-------------------------------------------\n";
 print $rf "Uptime: $uptime\n\n";

 # Per-PID analysis
 print $rf "PROCESS ANALYSIS\n";
 print $rf "-------------------------------------------\n";

 my %all_pids = (%pid_errors, %syscall_count);

 for my $pid (sort keys %all_pids) {
  my $cmd        = `ps -o comm= -p $pid 2>/dev/null`;
  chomp $cmd;
  my $err_total  = $pid_errors{$pid}->{total} // 0;
  my $confidence = calc_confidence($err_total);

  print $rf "\nPID $pid" . ($cmd ? " ($cmd)" : "") . "\n";
  print $rf "  Errors    : $err_total\n";
  print $rf "  Confidence: $confidence%\n";

  if (my $errs = $pid_errors{$pid}->{errors}) {
   for my $e (sort keys %$errs) {
    printf $rf "  %-15s %d occurrence(s)  --  %s\n",
           $e . ":", $errs->{$e}->{count}, ($error_causes{$e} // "Unknown");
   }
  }

  if ($syscall_count{$pid}) {
   my @top = sort { $syscall_count{$pid}{$b} <=> $syscall_count{$pid}{$a} }
                 keys %{$syscall_count{$pid}};
   @top = @top[0..4] if @top > 5;
   print $rf "  Top syscalls: " . join(", ", @top) . "\n";
  }
 }

 print $rf "\nGLOBAL SUMMARY\n";
 print $rf "-------------------------------------------\n";
 print $rf "Processes Traced : $total_traced\n";
 print $rf "Total Errors     : $total_errors\n";
 print $rf "Overall Confidence: " . calc_confidence($total_errors) . "%\n\n";

 # Recommendations
 print $rf "RECOMMENDATIONS\n";
 print $rf "-------------------------------------------\n";

 my $rec_count = 0;

 for my $pid (sort keys %pid_errors) {
  my $errs = $pid_errors{$pid}->{errors} // {};
  my $cmd  = `ps -o comm= -p $pid 2>/dev/null`;
  chomp $cmd;
  my $label = "PID $pid" . ($cmd ? " ($cmd)" : "");

  if (($errs->{EACCES}->{count}       // 0) > 0) {
   print $rf "  $label: Permission errors -- check file/directory ownership and modes\n";
   $rec_count++;
  }
  if (exists $errs->{ECONNREFUSED} && ($errs->{ECONNREFUSED}->{count} // 0) > 0) {
   print $rf "  $label: Connection refused -- verify target service is running and not blocked by firewall\n";
   $rec_count++;
  }
  if (($errs->{ENOENT}->{count}       // 0) > 0) {
   print $rf "  $label: Missing file or directory -- check config paths and symlinks\n";
   $rec_count++;
  }
  if (($errs->{ETIMEDOUT}->{count}    // 0) > 0) {
   print $rf "  $label: Connection timeouts -- check network reachability and DNS resolution\n";
   $rec_count++;
  }
  if (($errs->{SIGSEGV}->{count}      // 0) > 0) {
   print $rf "  $label: Segmentation fault detected -- review for crashes, run with --segs\n";
   $rec_count++;
  }
 }

 print $rf "  No specific recommendations\n" unless $rec_count;
 print $rf "\n";

 close $rf;
 print "Report written: $report_file\n";
}


# =============================================
# SYSTEM HEALTH
# Read load, memory, and I/O metrics for --status and --incident-mode.
# =============================================
sub check_system_health {
 my %h;

 # --- CPU count (for load thresholds) ---
 my $num_cpus = 0;
 if (open my $cpuf, "<", "/proc/cpuinfo") {
  while (<$cpuf>) { $num_cpus++ if /^processor\s*:/ }
  close $cpuf;
 }
 $num_cpus = 1 unless $num_cpus > 0;
 $h{num_cpus} = $num_cpus;

 # --- Load average (1-min) ---
 my $load1 = 0;
 if (open my $lf, "<", "/proc/loadavg") {
  my $line = <$lf>;
  close $lf;
  ($load1) = split /\s+/, $line if defined $line;
 }
 $h{load1}        = $load1 + 0;
 $h{load_status}  = $load1 >= $num_cpus * 2 ? "CRITICAL"
                  : $load1 >= $num_cpus     ? "WARNING"
                  :                           "OK";

 # --- Memory usage ---
 my ($mem_total, $mem_available) = (0, 0);
 if (open my $mf, "<", "/proc/meminfo") {
  while (<$mf>) {
   $mem_total     = $1 if /^MemTotal:\s+(\d+)/;
   $mem_available = $1 if /^MemAvailable:\s+(\d+)/;
  }
  close $mf;
 }
 my $mem_used_pct = $mem_total > 0
  ? int(100 * ($mem_total - $mem_available) / $mem_total)
  : 0;
 $h{mem_used_pct}  = $mem_used_pct;
 $h{mem_used_mb}   = int(($mem_total - $mem_available) / 1024);
 $h{mem_total_mb}  = int($mem_total / 1024);
 $h{mem_status}    = $mem_used_pct >= 95 ? "CRITICAL"
                   : $mem_used_pct >= 80 ? "WARNING"
                   :                       "OK";

 # --- I/O wait (iostat -c 1 1) ---
 $h{iowait}        = undef;
 $h{iowait_status} = "UNAVAILABLE";
 my $iostat_bin    = `which iostat 2>/dev/null`;
 chomp $iostat_bin;
 if ($iostat_bin) {
  my @lines     = `iostat -c 1 1 2>/dev/null`;
  my $next_data = 0;
  for my $line (@lines) {
   if ($line =~ /^avg-cpu/i) { $next_data = 1; next }
   if ($next_data && $line =~ /\S/) {
    my @vals   = grep { $_ ne '' } split /\s+/, $line;
    # iostat avg-cpu columns: %user %nice %system %iowait %steal %idle
    my $iowait = defined $vals[3] ? $vals[3] + 0 : 0;
    $h{iowait}        = $iowait;
    $h{iowait_status} = $iowait >= 50 ? "CRITICAL"
                      : $iowait >= 20 ? "WARNING"
                      :                 "OK";
    last;
   }
  }
 }

 # --- SAR availability ---
 my $sar_bin = `which sar 2>/dev/null`;
 chomp $sar_bin;
 $h{sar_available} = $sar_bin ? 1 : 0;

 # Populate global %health_summary with WARNING/CRITICAL findings
 if ($h{load_status} ne "OK") {
  $health_summary{"Load $h{load_status}"} =
   sprintf("%.2f (CPUs: %d, threshold %.0f)", $h{load1}, $h{num_cpus},
           $h{load_status} eq 'CRITICAL' ? $h{num_cpus} * 2 : $h{num_cpus});
 }
 if ($h{mem_status} ne "OK") {
  $health_summary{"Memory $h{mem_status}"} = sprintf("%d%%", $h{mem_used_pct});
 }
 if (defined $h{iowait} && $h{iowait_status} ne "OK") {
  $health_summary{"I/O Wait $h{iowait_status}"} = sprintf("%.1f%%", $h{iowait});
 }

 return \%h;
}

# Print the SERVER HEALTH block and return 1 if any metric is CRITICAL.
sub print_system_health {
 my ($h) = @_;
 say_out "\nSERVER HEALTH\n";
 say_out "=====================================\n";

 my $load_tag = $h->{load_status} eq 'CRITICAL' ? "  [" . c_red("CRITICAL")    . "]"
             : $h->{load_status} eq 'WARNING'  ? "  [" . c_yellow("WARNING") . "]"
             :                                   "";
 say_out sprintf("  Load Average  : %.2f  (CPUs: %d)%s\n",
                 $h->{load1}, $h->{num_cpus}, $load_tag);

 my $mem_tag  = $h->{mem_status} eq 'CRITICAL' ? "  [" . c_red("CRITICAL")    . "]"
              : $h->{mem_status} eq 'WARNING'   ? "  [" . c_yellow("WARNING") . "]"
              :                                   "";
 say_out sprintf("  Memory Usage  : %d%%  (%d MB / %d MB used)%s\n",
                 $h->{mem_used_pct}, $h->{mem_used_mb}, $h->{mem_total_mb}, $mem_tag);

 if (defined $h->{iowait}) {
  my $io_tag = $h->{iowait_status} eq 'CRITICAL' ? "  [" . c_red("CRITICAL")    . "]"
             : $h->{iowait_status} eq 'WARNING'   ? "  [" . c_yellow("WARNING") . "]"
             :                                      "";
  say_out sprintf("  I/O Wait      : %.1f%%%s\n", $h->{iowait}, $io_tag);
 } else {
  say_out "  I/O Wait      : unavailable (iostat not found)\n";
 }

 say_out "  SAR           : available\n" if $h->{sar_available};
 say_out "\n";

 return ($h->{load_status}    eq "CRITICAL" ||
         $h->{mem_status}     eq "CRITICAL" ||
         ($h->{iowait_status} // "") eq "CRITICAL");
}


# =============================================
# LOG PATH BUILDER
# New format: /var/log/smartstrace-logs/YYYY/MM/DD/HH/$service.$user.$pid.$ts
# =============================================
sub make_log_path {
 my ($timestamp) = @_;
 my @lt   = localtime($timestamp);
 my $yyyy = sprintf "%04d", $lt[5] + 1900;
 my $mm   = sprintf "%02d", $lt[4] + 1;
 my $dd   = sprintf "%02d", $lt[3];
 my $hh   = sprintf "%02d", $lt[2];

 # Service component
 my $svc_comp;
 if ($incident_mode) {
  $svc_comp = "incident_mode";
 } elsif ($status) {
  $svc_comp = "status";
 } elsif ($report) {
  $svc_comp = "report";
 } elsif ($auto_profile) {
  $svc_comp = "auto-profile";
 } elsif ($service && $service !~ /^-/) {
  ($svc_comp = $service) =~ s/,/_/g;
 } elsif (@profiles == 1) {
  $svc_comp = $profiles[0];
 } elsif (@profiles > 1) {
  $svc_comp = "multi-profile";
 } else {
  $svc_comp = "default";
 }

 # User component
 my $user_comp;
 if ($user && $user !~ /^-/) {
  ($user_comp = $user) =~ s/,/_/g;
 } else {
  my ($first_pid) = sort { $a <=> $b } grep { /^\d+$/ } keys %pid_errors;
  if ($first_pid) {
   $user_comp = `ps -o user= -p $first_pid 2>/dev/null`;
   chomp $user_comp;
   $user_comp =~ s/\s+//g;
  }
  $user_comp = "unknown" unless $user_comp;
 }

 # PID component
 my %seen_pids;
 my @all_pids = grep { !$seen_pids{$_}++ }
                (sort { $a <=> $b } keys %pid_errors,
                 sort { $a <=> $b } keys %syscall_count);
 my $pid_comp = @all_pids == 1 ? $all_pids[0]
              : @all_pids  > 1 ? "multi"
              :                  "unknown";

 my $dir      = "/var/log/smartstrace-logs/$yyyy/$mm/$dd/$hh";
 my $filename = "$svc_comp.$user_comp.$pid_comp.$timestamp";
 return ($dir, $filename);
}


# =============================================
# CHANGELOG
# =============================================
# =============================================
# LOG SUMMARY HELPERS
# =============================================

# parse_log_file($path)
# Parses a single smartstrace log file and returns a hashref of structured data.
# Returns undef if the file cannot be parsed (wrong format or unreadable).
sub parse_log_file {
 my ($path) = @_;
 my $basename = (split m{/}, $path)[-1];

 # Filename must match <mode>.<user>.<pid_comp>.<10-digit-timestamp>
 my ($mode, $user, $pid_comp, $ts) =
  $basename =~ /^([\w-]+)\.([\w.-]+)\.([\w]+)\.(\d{10})$/;
 return undef unless defined $ts;

 open(my $fh, '<', $path) or return undef;

 my %result = (
  file        => $path,
  basename    => $basename,
  mode        => $mode,
  user        => $user,
  pid_comp    => $pid_comp,
  timestamp   => $ts,
  run_date    => '',
  version     => '',
  profiles    => '',
  pids        => [],
  total_errors => 0,
 );

 my $current_pid  = undef;
 my $current_etype = undef;
 my $in_error_detail = 0;

 while (my $line = <$fh>) {
  chomp $line;

  # --- Header ---
  if ($line =~ /^smartstrace v(.+)$/)   { $result{version}  = $1; next }
  if ($line =~ /^Run date\s*:\s*(.+)$/) { $result{run_date} = $1; next }
  if ($line =~ /^Profiles\s*:\s*(.+)$/) { $result{profiles} = $1; next }

  # --- Section markers ---
  if ($line eq 'ERROR DETAIL')           { $in_error_detail = 1; $current_pid = undef; next }
  if ($line =~ /^CRITICAL PROCESS|^SHARED FAILURES|^================/) {
   $in_error_detail = 0; $current_pid = undef; $current_etype = undef; next
  }

  next unless $in_error_detail;

  # --- PID block header ---
  if ($line =~ /^\[PID (\d+)\](?:\s+\(([^)]+)\))?/) {
   my ($pid, $cmd) = ($1, $2 // '');
   $current_pid = {
    pid        => $pid,
    cmd        => $cmd,
    total      => 0,
    confidence => 0,
    cpu        => '',
    memory     => '',
    started    => '',
    uptime     => '',
    syscalls   => '',
    errors     => {},
   };
   push @{$result{pids}}, $current_pid;
   $current_etype = undef;
   next;
  }

  next unless $current_pid;

  # --- PID stats ---
  if ($line =~ /^\s+Total Errors\s*:\s*(\d+)/) {
   $current_pid->{total} = $1;
   $result{total_errors} += $1;
  }
  elsif ($line =~ /^\s+Confidence\s*:\s*(\d+)%/)    { $current_pid->{confidence} = $1 }
  elsif ($line =~ /^\s+CPU Usage\s*:\s*(.+)$/)       { $current_pid->{cpu}        = $1 }
  elsif ($line =~ /^\s+Memory\s*:\s*(.+)$/)          { $current_pid->{memory}     = $1 }
  elsif ($line =~ /^\s+Started\s*:\s*(.+)$/)         { $current_pid->{started}    = $1 }
  elsif ($line =~ /^\s+Running for\s*:\s*(.+)$/)     { $current_pid->{uptime}     = $1 }
  elsif ($line =~ /^\s+Top syscalls\s*:\s*(.+)$/)    { $current_pid->{syscalls}   = $1 }

  # --- Error type line: "  ETYPE:    N  --  Cause" ---
  elsif ($line =~ /^\s+(ENOENT|EACCES|ETIMEDOUT|ECONNREFUSED|SIGSEGV|EMFILE|ENOSPC|EADDRINUSE):\s+(\d+)\s+--\s+(.+)$/) {
   my ($etype, $count, $cause) = ($1, $2, $3);
   $current_etype = $etype;
   $current_pid->{errors}{$etype} = {
    count  => $count,
    cause  => $cause,
    paths  => [],
    addrs  => [],
    bursts => [],
   };
  }

  # --- Extracted path: "    /path/to/file   (N×)" ---
  elsif ($current_etype && $line =~ /^\s{4}(\/\S+)\s+\((\d+).?\)/) {
   push @{$current_pid->{errors}{$current_etype}{paths}}, [$1, $2];
  }

  # --- Extracted address: "    host:port   (N×)" or "[::1]:port" ---
  elsif ($current_etype && $line =~ /^\s{4}(\S+:\d+)\s+\((\d+).?\)/) {
   push @{$current_pid->{errors}{$current_etype}{addrs}}, [$1, $2];
  }

  # --- Burst annotation ---
  elsif ($current_etype && $line =~ /^\s+\[BURST:\s*(.+?)\]/) {
   push @{$current_pid->{errors}{$current_etype}{bursts}}, $1;
  }
 }

 close $fh;
 return \%result;
}


# summarize_logs($dir)
# Recursively scans $dir for smartstrace log files, parses them, and
# prints a structured summary to stdout.
# parse_raw_strace_file($path)
# Detects and parses a raw strace output file (e.g. from strace -ff -o prefix).
# Returns a hashref in the same shape as parse_log_file, with type=>'raw'.
# Returns undef if the file does not look like strace output.
sub parse_raw_strace_file {
 my ($path) = @_;
 my $basename = (split m{/}, $path)[-1];

 open(my $fh, '<', $path) or return undef;

 # Sample the first 30 non-empty lines for format detection
 my @sample;
 while (my $line = <$fh>) {
  chomp $line;
  next unless $line =~ /\S/;
  push @sample, $line;
  last if @sample >= 30;
 }
 return undef unless @sample;

 # Detect strace output signatures:
 #   -tt format:  "HH:MM:SS.uuuuuu syscall("
 #   -f  format:  "PID  syscall("  or  "PID  HH:MM:SS..."
 #   plain:       "syscall(...) = N"
 my $strace_count = grep {
     /^\d{2}:\d{2}:\d{2}\.\d+\s+\w/    # -tt: timestamp prefix
  || /^\d+\s+\d{2}:\d{2}:\d{2}\.\d+/  # -f -tt: PID + timestamp
  || /^\d+\s+\w+\(/                    # -f: PID + syscall
  || /^\w+\([^)]*\)\s*=\s*[-\d]/      # plain: syscall() = result
 } @sample;

 return undef unless $strace_count >= 3;

 # Infer PID from filename suffix (.DIGITS) -- strace -ff creates prefix.PID
 my ($prefix, $file_pid) = $basename =~ /^(.+)\.(\d+)$/ ? ($1, $2) : ($basename, undef);

 # Use file mtime as the run timestamp
 my $mtime = (stat($path))[9] // time();

 # Rewind and parse full file for known error codes
 seek($fh, 0, 0);

 my %err_counts;   # etype => total count
 my %err_paths;    # etype => { path => count }
 my %err_addrs;    # etype => { addr => count }

 while (my $line = <$fh>) {
  chomp $line;

  for my $etype (qw(ENOENT EACCES ETIMEDOUT ECONNREFUSED SIGSEGV EMFILE ENOSPC EADDRINUSE)) {
   next unless index($line, $etype) >= 0;

   $err_counts{$etype}++;

   # Path extraction for file-related errors
   if ($etype =~ /^(?:ENOENT|EACCES|ENOSPC)$/) {
    if ($line =~ /"(\/[^"]{1,512})"/) {
     $err_paths{$etype}{$1}++;
    }
   }

   # Address extraction for network errors
   if ($etype =~ /^(?:ECONNREFUSED|ETIMEDOUT|EADDRINUSE)$/) {
    # TCP: parse sin_addr and sin_port from connect() struct
    my $ip   = $line =~ /sin_addr=inet_addr\("([^"]+)"\)/ ? $1 : undef;
    my $port = $line =~ /sin_port=htons\((\d+)\)/         ? $1 : undef;
    if ($ip && $port) {
     $err_addrs{$etype}{"$ip:$port"}++;
    }
    # Unix socket: sun_path="/path/to/socket"
    elsif ($line =~ /sun_path="([^"]+)"/) {
     $err_addrs{$etype}{$1}++;
    }
   }
  }
 }
 close $fh;

 # Build errors structure (same shape as parse_log_file produces)
 my %errors;
 for my $etype (keys %err_counts) {
  my @paths = map  { [$_, $err_paths{$etype}{$_}] }
              sort { $err_paths{$etype}{$b} <=> $err_paths{$etype}{$a} }
              keys %{$err_paths{$etype} // {}};
  my @addrs = map  { [$_, $err_addrs{$etype}{$_}] }
              sort { $err_addrs{$etype}{$b} <=> $err_addrs{$etype}{$a} }
              keys %{$err_addrs{$etype} // {}};
  $errors{$etype} = {
   count  => $err_counts{$etype},
   cause  => lc($etype),
   paths  => \@paths,
   addrs  => \@addrs,
   bursts => [],
  };
 }

 my $total = 0;
 $total += $_ for values %err_counts;

 my $confidence = $total == 0 ? 0
                : $total  < 5 ? 30
                : $total < 20 ? 60
                : 90;

 my @lt = localtime($mtime);
 my $run_date = sprintf "%04d-%02d-%02d %02d:%02d:%02d",
                $lt[5]+1900,$lt[4]+1,$lt[3],$lt[2],$lt[1],$lt[0];

 return {
  file         => $path,
  basename     => $basename,
  mode         => 'raw-strace',
  user         => '',
  pid_comp     => $file_pid // $prefix,
  timestamp    => $mtime,
  run_date     => $run_date,
  version      => '',
  profiles     => '',
  type         => 'raw',
  prefix       => $prefix,
  pids         => [{
   pid        => $file_pid // '?',
   cmd        => $prefix,
   total      => $total,
   confidence => $confidence,
   cpu        => '',
   memory     => '',
   started    => '',
   uptime     => '',
   syscalls   => '',
   errors     => \%errors,
  }],
  total_errors => $total,
 };
}


sub summarize_logs {
 my ($dir) = @_;

 unless (-d $dir) {
  print "\n--sum-logs: directory not found: $dir\n\n";
  exit 1;
 }

 # Collect all regular files recursively; parse_log_file / parse_raw_strace_file
 # decide what each file is -- non-matching files return undef and are skipped.
 my @log_files;
 find(sub {
  return unless -f $_;
  push @log_files, $File::Find::name;
 }, $dir);

 unless (@log_files) {
  print "\n--sum-logs: no files found in $dir\n\n";
  exit 0;
 }

 # Parse all files -- try smartstrace format first, fall back to raw strace
 my @parsed;
 my ($ss_count, $raw_count) = (0, 0);
 for my $f (sort @log_files) {
  my $p = parse_log_file($f);
  if ($p) {
   $p->{type} //= 'smartstrace';
   $ss_count++;
  } else {
   $p = parse_raw_strace_file($f);
   if ($p) { $raw_count++ }
  }
  push @parsed, $p if $p;
 }

 unless (@parsed) {
  print "\n--sum-logs: no recognizable log files found in $dir\n\n";
  print "Accepted formats:\n";
  print "  smartstrace logs  -- named <mode>.<user>.<pid>.<timestamp>\n";
  print "  raw strace output -- any file whose content looks like strace output\n\n";
  exit 0;
 }

 # Group files into runs.
 #   smartstrace files: group by exact timestamp (all files from one invocation share it)
 #   raw strace files:  group by prefix + 5-minute mtime bucket (strace -ff per-PID files)
 my %runs;
 for my $p (@parsed) {
  my $run_key;
  if (($p->{type} // '') eq 'raw') {
   my $bucket = int($p->{timestamp} / 300);
   $run_key = "raw:$p->{prefix}:$bucket";
  } else {
   $run_key = "ss:$p->{timestamp}";
  }

  unless (exists $runs{$run_key}) {
   $runs{$run_key} = {
    run_key      => $run_key,
    timestamp    => $p->{timestamp},
    run_date     => $p->{run_date},
    mode         => $p->{mode},
    user         => $p->{user},
    profiles     => $p->{profiles},
    version      => $p->{version},
    type         => $p->{type} // 'smartstrace',
    files        => [],
    pids         => [],
    total_errors => 0,
   };
  }
  push @{$runs{$run_key}->{files}}, $p->{basename};
  push @{$runs{$run_key}->{pids}},  @{$p->{pids}};
  $runs{$run_key}->{total_errors} += $p->{total_errors};
 }

 # Sort runs newest-first by timestamp
 my @sorted_keys = sort { $runs{$b}->{timestamp} <=> $runs{$a}->{timestamp} } keys %runs;
 my $num_runs    = scalar @sorted_keys;
 my $num_files   = scalar @parsed;

 # Determine period from timestamp range across all runs
 my @all_ts    = map { $runs{$_}->{timestamp} } @sorted_keys;
 my $earliest  = (sort { $a <=> $b } @all_ts)[0];
 my $latest    = (sort { $b <=> $a } @all_ts)[0];
 my @elt = localtime($earliest); my @llt = localtime($latest);
 my $period_from = sprintf "%04d-%02d-%02d %02d:%02d",
                   $elt[5]+1900,$elt[4]+1,$elt[3],$elt[2],$elt[1];
 my $period_to   = sprintf "%04d-%02d-%02d %02d:%02d",
                   $llt[5]+1900,$llt[4]+1,$llt[3],$llt[2],$llt[1];

 # Build file-type summary string
 my @type_parts;
 push @type_parts, "$ss_count smartstrace"   if $ss_count;
 push @type_parts, "$raw_count raw strace"   if $raw_count;
 my $type_summary = join(", ", @type_parts);

 # -------------------------------------------------------
 # HEADER
 # -------------------------------------------------------
 print "\nsmartstrace v$VERSION  --  Log Summary\n";
 print "=====================================\n";
 printf "%-11s: %s\n", "Directory",  $dir;
 printf "%-11s: %d file%s (%s)\n",   "Files", $num_files, $num_files==1?"":"s", $type_summary;
 printf "%-11s: %d distinct run%s\n","Runs",  $num_runs,  $num_runs==1?"":"s";
 printf "%-11s: %s  --  %s\n",       "Period",$period_from, $period_to;
 print "\n";

 # -------------------------------------------------------
 # RUN COMPARISON
 # -------------------------------------------------------
 print "RUN COMPARISON\n";
 print "=====================================\n";
 printf "  %-22s %-18s %-12s %-8s %s\n",
        "Run Date", "Mode", "User", "PIDs", "Errors";
 printf "  %s %s %s %s %s\n",
        "-" x 22, "-" x 18, "-" x 12, "-" x 8, "-" x 7;

 for my $rk (@sorted_keys) {
  my $r    = $runs{$rk};
  my $ts   = $r->{timestamp};
  my $date = $r->{run_date} || do {
   my @lt = localtime($ts);
   sprintf "%04d-%02d-%02d %02d:%02d:%02d",
           $lt[5]+1900,$lt[4]+1,$lt[3],$lt[2],$lt[1],$lt[0];
  };
  my $pid_disp = scalar(@{$r->{pids}}) == 1
               ? $r->{pids}[0]{pid}
               : scalar(@{$r->{pids}}) . " PIDs";
  my $user_disp = length($r->{user}) ? $r->{user} : '(unknown)';
  printf "  %-22s %-18s %-12s %-8s %d\n",
         $date,
         substr($r->{mode},     0, 18),
         substr($user_disp,     0, 12),
         $pid_disp,
         $r->{total_errors};
 }
 print "\n";

 # -------------------------------------------------------
 # PROCESS ANALYSIS SUMMARY
 # -------------------------------------------------------
 print "PROCESS ANALYSIS SUMMARY\n";
 print "=====================================\n";

 for my $rk (@sorted_keys) {
  my $r  = $runs{$rk};
  my $ts = $r->{timestamp};
  next unless @{$r->{pids}};

  for my $pid_rec (@{$r->{pids}}) {
   my $cmd = $pid_rec->{cmd} ? "  ($pid_rec->{cmd})" : "";
   print "\n[PID $pid_rec->{pid}]$cmd\n";

   # Source line — omit user/mode fields that are empty for raw strace
   my $user_disp = length($r->{user}) ? $r->{user} : '(unknown)';
   printf "  %-13s: %s  |  mode: %s  |  user: %s\n",
          "Run", $r->{run_date} || $ts, $r->{mode}, $user_disp;
   printf "  %-13s: %s\n", "Log File",
          scalar(@{$r->{files}}) == 1 ? $r->{files}[0] : join(", ", @{$r->{files}});
   printf "  %-13s: %d  |  Confidence: %d%%\n",
          "Total Errors", $pid_rec->{total}, $pid_rec->{confidence};
   printf "  %-13s: %s\n", "CPU",      $pid_rec->{cpu}      if $pid_rec->{cpu};
   printf "  %-13s: %s\n", "Memory",   $pid_rec->{memory}   if $pid_rec->{memory};
   printf "  %-13s: %s\n", "Started",  $pid_rec->{started}  if $pid_rec->{started};
   printf "  %-13s: %s\n", "Running for", $pid_rec->{uptime} if $pid_rec->{uptime};
   print "\n";

   for my $etype (sort keys %{$pid_rec->{errors}}) {
    my $ed = $pid_rec->{errors}{$etype};
    printf "  %-15s %d  --  %s\n",
           "$etype:", $ed->{count}, $ed->{cause};

    # Burst annotations
    for my $b (@{$ed->{bursts}}) {
     print "    [BURST: $b]\n";
    }

    # Top 3 paths
    my @paths = @{$ed->{paths}};
    my $shown = 0;
    for my $p (@paths) {
     last if $shown >= 3;
     printf "    %-52s (%d×)\n", $p->[0], $p->[1];
     $shown++;
    }
    printf "    ... (%d more path%s)\n",
           scalar(@paths)-3, scalar(@paths)-3==1?"":"s"
     if @paths > 3;

    # Top 3 addresses
    my @addrs = @{$ed->{addrs}};
    $shown = 0;
    for my $a (@addrs) {
     last if $shown >= 3;
     printf "    %-52s (%d×)\n", $a->[0], $a->[1];
     $shown++;
    }
    printf "    ... (%d more address%s)\n",
           scalar(@addrs)-3, scalar(@addrs)-3==1?"":"es"
     if @addrs > 3;
   }

   printf "  %-13s: %s\n", "Top syscalls", $pid_rec->{syscalls}
    if $pid_rec->{syscalls};
  }
 }
 print "\n";

 # -------------------------------------------------------
 # CROSS-RUN PATTERNS
 # -------------------------------------------------------
 # Collect: for each (etype,target) -> which ts values it appeared in
 my %path_runs;  # "$etype\0$path" => { ts => 1, pids => {pid=>1} }
 my %addr_runs;  # "$etype\0$addr" => { ts => 1, pids => {pid=>1} }
 my %pid_runs;   # "$pid\0$cmd"    => { ts => 1, errors => N }

 for my $rk (@sorted_keys) {
  my $r = $runs{$rk};
  for my $pid_rec (@{$r->{pids}}) {
   my $key = "$pid_rec->{pid}\0$pid_rec->{cmd}";
   $pid_runs{$key}{$rk} = $pid_rec->{total};

   for my $etype (keys %{$pid_rec->{errors}}) {
    my $ed = $pid_rec->{errors}{$etype};
    for my $p (@{$ed->{paths}}) {
     my $k = "$etype\0$p->[0]";
     $path_runs{$k}{ts}{$rk} = 1;
     $path_runs{$k}{pids}{$pid_rec->{pid}} = 1;
    }
    for my $a (@{$ed->{addrs}}) {
     my $k = "$etype\0$a->[0]";
     $addr_runs{$k}{ts}{$rk} = 1;
     $addr_runs{$k}{pids}{$pid_rec->{pid}} = 1;
    }
   }
  }
 }

 # Filter to those appearing in 2+ runs
 my @recurring_paths = sort {
  scalar(keys %{$path_runs{$b}{ts}}) <=> scalar(keys %{$path_runs{$a}{ts}})
 } grep { scalar(keys %{$path_runs{$_}{ts}}) >= 2 } keys %path_runs;

 my @recurring_addrs = sort {
  scalar(keys %{$addr_runs{$b}{ts}}) <=> scalar(keys %{$addr_runs{$a}{ts}})
 } grep { scalar(keys %{$addr_runs{$_}{ts}}) >= 2 } keys %addr_runs;

 my @recurring_pids = sort {
  scalar(keys %{$pid_runs{$b}}) <=> scalar(keys %{$pid_runs{$a}})
 } grep { scalar(keys %{$pid_runs{$_}}) >= 2 } keys %pid_runs;

 if (@recurring_paths || @recurring_addrs || @recurring_pids) {
  print "CROSS-RUN PATTERNS\n";
  print "=====================================\n";

  if (@recurring_paths || @recurring_addrs) {
   print "  Persistent errors (appearing in 2+ runs):\n\n";

   for my $k (@recurring_addrs) {
    my ($etype, $addr) = split /\0/, $k, 2;
    my $n    = scalar keys %{$addr_runs{$k}{ts}};
    my $pids = join(", ", sort { $a <=> $b } keys %{$addr_runs{$k}{pids}});
    printf "  %-15s -> %-40s  %d of %d runs  |  PIDs: %s\n",
           $etype, $addr, $n, $num_runs, $pids;
   }

   for my $k (@recurring_paths) {
    my ($etype, $path) = split /\0/, $k, 2;
    my $n    = scalar keys %{$path_runs{$k}{ts}};
    my $pids = join(", ", sort { $a <=> $b } keys %{$path_runs{$k}{pids}});
    printf "  %-15s    %-40s  %d of %d runs  |  PIDs: %s\n",
           $etype, $path, $n, $num_runs, $pids;
   }
   print "\n";
  }

  if (@recurring_pids) {
   print "  PIDs appearing in multiple runs:\n\n";
   for my $k (@recurring_pids) {
    my ($pid, $cmd) = split /\0/, $k, 2;
    my $n      = scalar keys %{$pid_runs{$k}};
    my $total  = 0;
    $total    += $_ for values %{$pid_runs{$k}};
    my $label  = $cmd ? "PID $pid  ($cmd)" : "PID $pid";
    printf "  %-30s  errors in %d of %d runs  |  %d total errors\n",
           $label, $n, $num_runs, $total;
   }
   print "\n";
  }
 }

 print "=====================================\n\n";
}


sub show_change_log {
 print "\nsmartstrace v$VERSION\n";
 print "=====================================\n";

 if ($full) {
  for my $ver (sort ver_cmp keys %changelog) {
   print "\nVersion $ver\n";
   print "-------------------------------------\n";
   for my $entry (@{$changelog{$ver}}) {
    print "  - $entry\n";
   }
  }

  print "\nLegacy Change Log\n";
  print "-------------------------------------\n";
  for my $group (sort keys %legacy_changelog) {
   print "\n$group\n";
   for my $entry (@{$legacy_changelog{$group}}) {
    print "  $entry\n";
   }
  }

 } else {
  my ($latest) = sort ver_cmp keys %changelog;
  print "\nVersion $latest\n";
  print "-------------------------------------\n";
  for my $entry (@{$changelog{$latest}}) {
   print "  - $entry\n";
  }
  print "\n(use --change-log --full to see full history)\n";
 }

 print "\n=====================================\n\n";
}

# --info is a standalone mode; combining it with operational flags is not meaningful.
# --help is the only permitted companion (for contextual inline help).
if ($info && !$help) {
 my @operational = grep {
  /^--(run|status|quick|incident-mode|profile|profile-check|auto-profile|
      service|user|pid|log|report|json-only|json-stream|segs|csf|similar|
      watch|alert-errors|alert-cpu|top|cpu|min-errors|exclude-profile|
      context|context-only|no-color|change-log)/x
 } @raw_argv;
 if (@operational) {
  print "\n--info is a standalone flag and cannot be combined with operational flags.\n";
  print "  Permitted: smartstrace --info\n";
  print "             smartstrace --info --help\n\n";
  print "Flags provided that are not compatible: " . join(", ", @operational) . "\n\n";
  exit 1;
 }
}

if ($info && !$help) {
 print "\nsmartstrace v$VERSION -- Guided Overview\n";
 print "=====================================\n\n";

 print "WHAT IS SMARTSTRACE?\n";
 print "-------------------------------------\n";
 print "smartstrace is an intelligent wrapper around the Linux strace utility.\n";
 print "It attaches to running processes, captures system call traces, classifies\n";
 print "errors by type (ENOENT, EACCES, ECONNREFUSED, ETIMEDOUT, SIGSEGV, EMFILE,\n";
 print "ENOSPC, EADDRINUSE), and produces structured summaries with actionable hints.\n";
 print "It requires root (or strace permission) to attach to processes.\n\n";

 print "WHO SHOULD USE IT?\n";
 print "-------------------------------------\n";
 print "  System administrators  -- diagnosing high load, service failures, crashes\n";
 print "  Support engineers      -- reproducing and isolating user-reported issues\n";
 print "  Security analysts      -- spotting unexpected file/network activity\n";
 print "  DevOps / on-call       -- rapid triage during incidents\n\n";

 print "QUICK-START WORKFLOWS\n";
 print "-------------------------------------\n";
 print "1. First look at a live server (no log required):\n";
 print "     smartstrace --quick\n\n";
 print "2. Full server health + error triage (recommended for incidents):\n";
 print "     smartstrace --incident-mode\n\n";
 print "3. Check which profiles are running before committing to a trace:\n";
 print "     smartstrace --profile-check\n\n";
 print "4. Trace a specific service and get a written report:\n";
 print "     smartstrace --service=nginx --report\n\n";
 print "5. Trace a specific PID (e.g. a known-bad process):\n";
 print "     smartstrace --pid=12345 --quick\n\n";
 print "6. Multiple PIDs at once (comma-separated):\n";
 print "     smartstrace --pid=12345,67890 --quick\n\n";

 print "COMMON DIAGNOSTIC SCENARIOS\n";
 print "-------------------------------------\n";
 print "Server is slow / high load:\n";
 print "  smartstrace --status\n";
 print "  smartstrace --incident-mode --top=20\n\n";
 print "PHP application errors (500s, timeouts, permission issues):\n";
 print "  smartstrace --profile=php --log\n";
 print "  smartstrace --profile=fpm --context-only --context=5\n\n";
 print "MySQL/MariaDB connection failures:\n";
 print "  smartstrace --profile=mysql --log\n";
 print "  smartstrace --service=mysql --report\n\n";
 print "Nginx / Apache not responding:\n";
 print "  smartstrace --profile=nginx --quick\n";
 print "  smartstrace --service=httpd,nginx --log\n\n";
 print "Redis connectivity issues:\n";
 print "  smartstrace --profile=redis --quick\n\n";
 print "Cron jobs failing silently:\n";
 print "  smartstrace --profile=cron --log\n\n";
 print "File descriptor / disk space exhaustion:\n";
 print "  smartstrace --quick          (EMFILE and ENOSPC show in PROCESS ANALYSIS)\n";
 print "  smartstrace --incident-mode  (health check also covers disk/load thresholds)\n\n";
 print "Port conflict (process can't bind to address):\n";
 print "  smartstrace --profile=network --quick\n";
 print "                               (EADDRINUSE surfaces with address extracted)\n\n";
 print "Segfault / crashing process:\n";
 print "  smartstrace --segs --quick\n";
 print "  smartstrace --segs --log     (full context written to log)\n\n";
 print "User-specific issues (e.g. one customer causing load):\n";
 print "  smartstrace --profile=user --user=someuser --log\n\n";
 print "Firewall blocking connections:\n";
 print "  smartstrace --csf --profile=network --log\n";
 print "                               (ECONNREFUSED addresses cross-checked vs csf.deny)\n\n";
 print "Reviewing a manually captured strace session:\n";
 print "  # After running:  strace -Tttffvvyys4096 -o /root/cptechs/\$ticket/trace -p \$PID\n";
 print "  smartstrace --sum-logs=/root/cptechs/\$ticket/\n";
 print "                               (auto-detects raw strace files, extracts errors,\n";
 print "                                groups prefix.PID files from -ff into one run)\n\n";
 print "Reviewing smartstrace incident captures across a day:\n";
 print "  smartstrace --sum-logs=/var/log/smartstrace-logs/\$(date +%%Y/%%m/%%d)/\n";
 print "                               (RUN COMPARISON + CROSS-RUN PATTERNS across all runs)\n\n";

 print "USEFUL FLAG COMBINATIONS\n";
 print "-------------------------------------\n";
 printf "  %-45s %s\n", "--incident-mode --top=20",               "Triage top 20 PIDs by error count";
 printf "  %-45s %s\n", "--profile=all --exclude-profile=cron",   "All profiles except cron";
 printf "  %-45s %s\n", "--profile=php,mysql --log --report",     "PHP + MySQL trace, log and report";
 printf "  %-45s %s\n", "--status --alert-errors=10",             "Alert when any PID hits 10+ errors";
 printf "  %-45s %s\n", "--watch='ECONNREFUSED.*3306' --run",     "Live alert on MySQL connection refusals";
 printf "  %-45s %s\n", "--auto-profile --log",                   "Auto-detect running services, log all";
 printf "  %-45s %s\n", "--context=5 --context-only --quick",     "Show 5-line strace context per error";
 printf "  %-45s %s\n", "--min-errors=10 --incident-mode",        "Only report PIDs with 10+ errors";
 printf "  %-45s %s\n", "--no-color --incident-mode",             "Strip ANSI color (for log redirection)";
 printf "  %-45s %s\n", "--json-only --status",                   "Machine-readable JSON output";
 printf "  %-45s %s\n", "--sum-logs=/root/cptechs/\$ticket/",     "Summarize raw strace files from a ticket dir";
 printf "  %-45s %s\n", "--sum-logs=/var/log/smartstrace-logs/\$(date +%%Y/%%m/%%d)/",
                                                                   "Review today's smartstrace captures";
 print "\n";

 print "RECOMMENDED NEXT STEPS\n";
 print "-------------------------------------\n";
 print "  smartstrace --help               full flag reference\n";
 print "  smartstrace --help --profile     detailed profile documentation\n";
 print "  smartstrace --help --incident-mode\n";
 print "  smartstrace --change-log         version history\n\n";

 print "=====================================\n\n";
 exit 0;
}

# --sum-logs is a standalone mode; it reads existing logs and cannot be combined
# with live-tracing flags.
if ($sum_logs && !$help) {
 my @operational = grep {
  /^--(run|status|quick|incident-mode|profile|profile-check|auto-profile|
      service|user|pid|log|report|json-only|json-stream|segs|csf|similar|
      watch|alert-errors|alert-cpu|top|cpu|min-errors|exclude-profile|
      context|context-only|no-color|change-log|info)/x
 } @raw_argv;
 if (@operational) {
  print "\n--sum-logs is a standalone flag and cannot be combined with operational flags.\n";
  print "  Usage: smartstrace --sum-logs=/path/to/logdir\n\n";
  print "Flags provided that are not compatible: " . join(", ", @operational) . "\n\n";
  exit 1;
 }
}

if ($sum_logs && !$help) {
 summarize_logs($sum_logs);
 exit 0;
}

if ($change_log && !$help) {
 show_change_log();
 exit 0;
}


# =============================================
# HELP SYSTEM
# =============================================
if ($help) {

 print "\nsmartstrace v$VERSION\n";
 print "=====================================\n";

 my $matched = 0;

 # --- invalid flag suggestions ---
 my @known_flags = map { "--$_" } keys %script_flag_help;

 for my $arg (@raw_argv) {

  if ($arg =~ /^--([a-z][a-z0-9\-]+)$/i) {
   my $input = $arg;
   next if grep { $input eq $_ } @known_flags;
   my @suggestions = sort {
    levenshtein($input, $a) <=> levenshtein($input, $b)
   } @known_flags;
   if (@suggestions && levenshtein($input, $suggestions[0]) <= 3) {
    print "\nInvalid flag: $input\n\n";
    print "Did you mean:\n  $suggestions[0]\n\n";
    exit 0;
   }
  }

  if ($arg =~ /^-([a-z]{4,})$/i) {
   my $input = "--$1";
   my @suggestions = sort {
    levenshtein($input, $a) <=> levenshtein($input, $b)
   } @known_flags;
   if (@suggestions && levenshtein($input, $suggestions[0]) <= 3) {
    print "\nInvalid flag: $arg\n\n";
    print "Did you mean:\n  $suggestions[0]\n\n";
    exit 0;
   }
  }
 }

 # --- profile help ---
 if (defined $profile || grep { /^--profile/ } @raw_argv) {
  print "\n--profile=<type1,type2,...>\n";
  print "-------------------------------------\n";
  print "Run one or more analysis profiles\n\n";
  for my $p (sort keys %profile_help) {
   print "  $p\n";
   print "    $profile_help{$p}->{desc}\n";
   print "    Targets : $profile_help{$p}->{processes}\n";
   if ($profile_help{$p}->{behavior}) {
    print "    Behavior: $profile_help{$p}->{behavior}\n";
   }
   print "    Example : $profile_help{$p}->{example}\n\n";
  }
  print "Note: --profile=user traces all users by default.\n";
  print "      Add --user=<name> to limit to specific user(s).\n\n";
  $matched = 1;
 }

 # --- profile-check help ---
 if ($profile_check || grep { /^--profile-check/ } @raw_argv) {
  print "\n--profile-check\n";
  print "-------------------------------------\n";
  print "$script_flag_help{'profile-check'}->{desc}\n\n";
  print "Example:\n  $script_flag_help{'profile-check'}->{example}\n\n";
  $matched = 1;
 }

 # --- auto-profile help ---
 if ($auto_profile || grep { /^--auto-profile/ } @raw_argv) {
  print "\n--auto-profile\n";
  print "-------------------------------------\n";
  print "$script_flag_help{'auto-profile'}->{desc}\n\n";
  print "Detects: php (pgrep -f php), mysql (pgrep mysqld),\n";
  print "         network (active TCP connections via ss), io (always)\n\n";
  print "Example:\n  $script_flag_help{'auto-profile'}->{example}\n\n";
  $matched = 1;
 }

 # --- incident-mode help ---
 if ($incident_mode || grep { /^--incident-mode/ } @raw_argv) {
  print "\n--incident-mode\n";
  print "-------------------------------------\n";
  print "$script_flag_help{'incident-mode'}->{desc}\n\n";
  print "Self-contained -- no additional flags required.\n";
  print "Output sections:\n";
  print "  Server Health    -- load, memory, I/O wait with WARNING/CRITICAL thresholds\n";
  print "  Profile Status   -- which profiles are active and what they found\n";
  print "  Service Status   -- running state of all supported services\n";
  print "  User Status      -- top users by error count after tracing\n";
  print "  Process Analysis -- top-N PIDs sorted by error count\n\n";
  print "Default top 10 PIDs (override with --top=N)\n";
  print "Extended error detail for high-error PIDs written to log only\n\n";
  print "Example:\n  $script_flag_help{'incident-mode'}->{example}\n";
  print "  smartstrace --incident-mode --top=20\n\n";
  $matched = 1;
 }

 # --- status help ---
 if ($status || grep { /^--status$/ } @raw_argv) {
  print "\n--status\n";
  print "-------------------------------------\n";
  print "Runs a server health check followed by a short analysis across all profiles\n\n";
  print "Health check covers: load average, memory usage, I/O wait\n";
  print "  WARNING: elevated metrics  |  CRITICAL: metrics suggest active problem\n";
  print "  If CRITICAL conditions are detected, --incident-mode is suggested\n\n";
  print "Profiles used: " . join(", ", sort keys %profile_help) . "\n";
  print "Default top 5 PIDs (override with --top=N)\n\n";
  print "Example:\n  smartstrace --status\n";
  print "  smartstrace --status --top=10\n\n";
  $matched = 1;
 }

 # --- user help ---
 if (defined $user || grep { /^--user/ } @raw_argv) {
  print "\n--user=<user1,user2,...>\n";
  print "-------------------------------------\n";
  print "$script_flag_help{user}->{desc}\n\n";
  print "Comma-separate multiple usernames to trace all at once.\n";
  print "When used with --profile=user, limits tracing to those user(s) only.\n";
  print "Without --user, --profile=user traces top-N processes across all users.\n\n";
  print "Example:\n  $script_flag_help{user}->{example}\n\n";
  $matched = 1;
 }

 # --- service help ---
 if (defined $service || grep { /^--service/ } @raw_argv) {
  print "\n--service=<name1,name2,...>\n";
  print "-------------------------------------\n";
  print "$script_flag_help{service}->{desc}\n\n";
  print "Comma-separate multiple services to trace all at once.\n\n";
  print "Available services:\n  @supported_services\n\n";
  print "Example:\n  $script_flag_help{service}->{example}\n\n";
  print "Notes:\n  PIDs are refreshed each loop iteration in --run mode\n";
  $matched = 1;
 }

 # --- top help ---
 if (defined $top_n || grep { /^--top/ } @raw_argv) {
  print "\n--top=N\n";
  print "-------------------------------------\n";
  print "$script_flag_help{top}->{desc}\n\n";
  print "Context-sensitive defaults:\n";
  print "  --incident-mode  default 10\n";
  print "  --status         default 5\n";
  print "  general use      default 5\n\n";
  print "Examples:\n";
  print "  smartstrace --status --top=10\n";
  print "  smartstrace --incident-mode --top=20\n\n";
  $matched = 1;
 }

 # --- alert flags help ---
 if (defined $alert_errors || defined $alert_cpu ||
     grep { /^--alert/ } @raw_argv) {
  print "\n--alert-errors=N  /  --alert-cpu=N\n";
  print "-------------------------------------\n";
  print "$script_flag_help{'alert-errors'}->{desc}\n";
  print "$script_flag_help{'alert-cpu'}->{desc}\n\n";
  print "Note: --cpu=N filters which processes are traced.\n";
  print "      --alert-cpu=N triggers an alert during monitoring.\n";
  print "      These are independent thresholds.\n\n";
  print "Examples:\n";
  print "  $script_flag_help{'alert-errors'}->{example}\n";
  print "  $script_flag_help{'alert-cpu'}->{example}\n\n";
  $matched = 1;
 }

 # --- json flags help ---
 if ($json_only || $json_stream || grep { /^--json/ } @raw_argv) {
  print "\n--json-only  /  --json-stream\n";
  print "-------------------------------------\n";
  print "$script_flag_help{'json-only'}->{desc}\n";
  print "$script_flag_help{'json-stream'}->{desc}\n\n";
  print "json-only output structure:\n";
  print "  { version, timestamp, profiles, processes: { PID: { errors, confidence, top_syscalls } }, global }\n\n";
  print "json-stream events: trace_start, error, alert_errors, alert_cpu, trace_end\n\n";
  print "Examples:\n";
  print "  $script_flag_help{'json-only'}->{example}\n";
  print "  $script_flag_help{'json-stream'}->{example}\n\n";
  $matched = 1;
 }

 # --- segs help ---
 if ($segs || grep { /^--segs/ } @raw_argv) {
  print "\n--segs\n";
  print "-------------------------------------\n";
  print "$script_flag_help{segs}->{desc}\n\n";
  print "Also cross-references recent kernel segfault entries from dmesg.\n\n";
  print "Example:\n  $script_flag_help{segs}->{example}\n\n";
  $matched = 1;
 }

 # --- csf help ---
 if ($csf || grep { /^--csf/ } @raw_argv) {
  print "\n--csf\n";
  print "-------------------------------------\n";
  print "$script_flag_help{csf}->{desc}\n\n";
  print "Checks: CSF installation, active/disabled status, LFD daemon,\n";
  print "        PIDs with ECONNREFUSED/ETIMEDOUT (possible firewall blocks)\n\n";
  print "Example:\n  $script_flag_help{csf}->{example}\n\n";
  $matched = 1;
 }

 # --- similar help ---
 if ($similar || grep { /^--similar/ } @raw_argv) {
  print "\n--similar\n";
  print "-------------------------------------\n";
  print "$script_flag_help{similar}->{desc}\n\n";
  print "Builds a top-5 syscall fingerprint for each traced PID and groups\n";
  print "PIDs that share 3 or more syscalls in common.\n\n";
  print "Example:\n  $script_flag_help{similar}->{example}\n\n";
  $matched = 1;
 }

 # --- report help ---
 if ($report || grep { /^--report/ } @raw_argv) {
  print "\n--report\n";
  print "-------------------------------------\n";
  print "$script_flag_help{report}->{desc}\n\n";
  print "Includes: per-PID error breakdown, top syscalls, confidence scores,\n";
  print "          global summary, and recommended next steps.\n\n";
  print "Falls back to current directory if /var/log/smartstrace-logs/ is not writable.\n\n";
  print "Example:\n  $script_flag_help{report}->{example}\n\n";
  $matched = 1;
 }

 # --- changelog help ---
 if (defined $change_log || grep { /^--change-log$/ } @raw_argv) {
  print "\n--change-log\n";
  print "-------------------------------------\n";
  print "$script_flag_help{'change-log'}->{desc}\n\n";
  print "Example:\n  $script_flag_help{'change-log'}->{example}\n\n";
  $matched = 1;
 }

 # --- watch / watch-cooldown help ---
 if (defined $watch || defined $watch_cooldown || grep { /^--watch/ } @raw_argv) {
  print "\n--watch=PATTERN  /  --watch-cooldown=N\n";
  print "-------------------------------------\n";
  print "$script_flag_help{watch}->{desc}\n";
  print "$script_flag_help{'watch-cooldown'}->{desc}\n\n";
  print "Examples:\n";
  print "  $script_flag_help{watch}->{example}\n";
  print "  $script_flag_help{'watch-cooldown'}->{example}\n\n";
  $matched = 1;
 }

 # --- min-errors help ---
 if (defined $min_errors || grep { /^--min-errors/ } @raw_argv) {
  print "\n--min-errors=N\n";
  print "-------------------------------------\n";
  print "$script_flag_help{'min-errors'}->{desc}\n\n";
  print "Example:\n  $script_flag_help{'min-errors'}->{example}\n\n";
  $matched = 1;
 }

 # --- no-color help ---
 if (defined $no_color || grep { /^--no-color/ } @raw_argv) {
  print "\n--no-color\n";
  print "-------------------------------------\n";
  print "$script_flag_help{'no-color'}->{desc}\n\n";
  print "Example:\n  $script_flag_help{'no-color'}->{example}\n\n";
  $matched = 1;
 }

 # --- exclude-profile help ---
 if (defined $exclude_profile || grep { /^--exclude-profile/ } @raw_argv) {
  print "\n--exclude-profile=PROFILE[,PROFILE,...]\n";
  print "-------------------------------------\n";
  print "$script_flag_help{'exclude-profile'}->{desc}\n\n";
  print "Example:\n  $script_flag_help{'exclude-profile'}->{example}\n\n";
  $matched = 1;
 }

 # --- sum-logs help ---
 if (defined $sum_logs || grep { /^--sum-logs/ } @raw_argv) {
  print "\n--sum-logs=PATH\n";
  print "-------------------------------------\n";
  print "$script_flag_help{'sum-logs'}->{desc}\n\n";
  print "File format detection:\n";
  print "  smartstrace logs  -- identified by filename pattern <mode>.<user>.<pid>.<ts>\n";
  print "  raw strace output -- auto-detected from content (strace -ff, -tt, -f output)\n";
  print "  Other files in the directory are silently skipped.\n\n";
  print "Output sections:\n";
  print "  RUN COMPARISON          -- all runs sorted newest-first; mode shows 'raw-strace'\n";
  print "                            for files not produced by smartstrace\n";
  print "  PROCESS ANALYSIS SUMMARY -- per-PID error detail with extracted paths/addresses\n";
  print "  CROSS-RUN PATTERNS      -- errors and targets recurring across 2+ runs\n\n";
  print "Raw strace tip: when using strace -ff -o /path/prefix, point --sum-logs at the\n";
  print "  containing directory and all prefix.PID files will be grouped as one run:\n";
  print "  strace -Tttffvvyys4096 -o /root/cptechs/12345/trace -p \$PID\n";
  print "  smartstrace --sum-logs=/root/cptechs/12345/\n\n";
  print "Tip: Be as specific as possible with the path to minimize scan time:\n";
  print "  --sum-logs=/var/log/smartstrace-logs/2026/05/22/14   (one hour)\n";
  print "  --sum-logs=/var/log/smartstrace-logs/2026/05/22      (one day)\n";
  print "  --sum-logs=/var/log/smartstrace-logs/2026/05         (one month)\n\n";
  print "Example:\n  $script_flag_help{'sum-logs'}->{example}\n\n";
  $matched = 1;
 }

 # --- info help ---
 if ($info || grep { /^--info$/ } @raw_argv) {
  print "\n--info\n";
  print "-------------------------------------\n";
  print "$script_flag_help{info}->{desc}\n\n";
  print "Example:\n  $script_flag_help{info}->{example}\n\n";
  $matched = 1;
 }

 # --- context / context-only help ---
 if (defined $context_n || $context_only || grep { /^--context/ } @raw_argv) {
  print "\n--context=N  /  --context-only\n";
  print "-------------------------------------\n";
  print "$script_flag_help{context}->{desc}\n";
  print "$script_flag_help{'context-only'}->{desc}\n\n";
  print "Notes:\n";
  print "  --context=N sets the rolling capture window (lines before each error).\n";
  print "  --context-only prints those captured blocks to terminal output under\n";
  print "  each PID section in PROCESS ANALYSIS. Error lines are highlighted.\n";
  print "  Both flags work independently: --context=N also affects log output;\n";
  print "  --context-only without --context uses the default 3-line window.\n\n";
  print "Examples:\n";
  print "  $script_flag_help{context}->{example}\n";
  print "  $script_flag_help{'context-only'}->{example}\n\n";
  $matched = 1;
 }

 # --- strace flag help ---
 my @strace_args;
 my %script_long_flags = map { $_ => 1 } qw(
  help profile profile-check auto-profile service user change-log run status
  quick json-only json-stream incident-mode segs csf similar report log full
  alert-errors alert-cpu top cpu pid watch watch-cooldown
  min-errors no-color exclude-profile context context-only info sum-logs
 );

 for my $arg (@raw_argv) {
  if ($arg =~ /^-[^-]/) {
   push @strace_args, $arg;
  }
  elsif ($arg =~ /^--([A-Za-z][A-Za-z0-9\-]*)/) {
   next if $script_long_flags{$1};
   (my $fixed = $arg) =~ s/^--/-/;
   push @strace_args, $fixed;
  }
 }

 if (@strace_args) {
  print "\nSTRACE FLAGS (Detected)\n";
  print "-------------------------------------\n";
  my %seen;
  for my $arg (@strace_args) {
   for my $f (parse_flags($arg)) {
    $seen{$f->[0]} = $f;
   }
  }
  for my $flag (sort keys %seen) {
   my ($f,undef,$valid) = @{$seen{$flag}};
   my $desc = $strace_flag_help{$f};
   if ($valid && defined $desc) {
    printf "  -%-9s %s\n", $f, $desc;
   } else {
    printf "  -%-9s %s\n", $f, "Unknown";
   }
  }
  print "\nNotes:\n";
  print "  $strace_flag_notes{combined}\n";
  print "  $strace_flag_notes{values}\n\n";
  print "Full STRACE Flag Reference:\n";
  print "-------------------------------------\n";
  for my $f (sort keys %strace_flag_help) {
   printf "  -%-9s %s\n", $f, $strace_flag_help{$f};
  }
  print "\n";
  $matched = 1;
 }

 # --- full help ---
 unless ($matched) {
  print "\nUSAGE:\n";
  print "  smartstrace [options] [strace flags]\n\n";
  print "SCRIPT FLAGS:\n";
  print "-------------------------------------\n";
  for my $flag (sort keys %script_flag_help) {
   printf "  --%-16s %s\n", $flag, $script_flag_help{$flag}->{desc};
  }
  print "\nPROFILES:\n";
  print "-------------------------------------\n";
  for my $p (sort keys %profile_help) {
   printf "  %-10s %s  [targets: %s]\n",
          $p, $profile_help{$p}->{desc}, $profile_help{$p}->{processes};
  }
  print "\nSTRACE FLAGS:\n";
  print "-------------------------------------\n";
  for my $f (sort keys %strace_flag_help) {
   printf "  -%-12s %s\n", $f, $strace_flag_help{$f};
  }
  print "\nNotes:\n";
  print "  $strace_flag_notes{combined}\n";
  print "  $strace_flag_notes{values}\n\n";
  print "Examples:\n";
  print "  smartstrace --quick\n";
  print "  smartstrace --status\n";
  print "  smartstrace --status --top=10\n";
  print "  smartstrace --incident-mode\n";
  print "  smartstrace --incident-mode --top=20\n";
  print "  smartstrace --profile=network,php\n";
  print "  smartstrace --profile=all                   (all profiles)\n";
  print "  smartstrace --profile=all --exclude-profile=cron,redis\n";
  print "  smartstrace --profile=user                  (all users, grouped)\n";
  print "  smartstrace --profile=user --user=apache    (apache only)\n";
  print "  smartstrace --service=httpd,nginx\n";
  print "  smartstrace --service=all                   (all services)\n";
  print "  smartstrace --auto-profile\n";
  print "  smartstrace --json-only --status\n";
  print "  smartstrace --alert-errors=10 --alert-cpu=80 --run\n";
  print "  smartstrace --min-errors=5 --incident-mode\n";
  print "  smartstrace --context-only --quick\n";
  print "  smartstrace --context=5 --context-only --profile=php\n";
  print "  smartstrace --segs --csf --report\n";
  print "  smartstrace --sum-logs=/var/log/smartstrace-logs/2026/05/22\n\n";
  print "Tip: Run --info for a guided overview with scenario-based examples.\n";
  print "     Run --sum-logs=PATH to summarize previously captured log files.\n\n";
 }

 print "=====================================\n\n";
 exit 0;
}


# =============================================
# NORMALIZE
# =============================================
$profile     ||= "";
$user        ||= "";
$pid_filter  ||= "";

# top_n default is context-sensitive; --top=N always overrides.
unless (defined $top_n && $top_n =~ /^\d+$/) {
 $top_n = $incident_mode ? 10 : 5;
}
$cpu_threshold = 50 unless defined $cpu_threshold && $cpu_threshold =~ /^\d+$/;
# --context=N: number of lines of context captured around each error. Default 3.
$context_n = 3 unless defined $context_n && $context_n =~ /^\d+$/ && $context_n >= 1;

if ($status) {
 @profiles = sort keys %profile_help;
}
elsif ($profile) {
 $profile =~ s/\s+//g;
 if (lc($profile) eq 'all') {
  @profiles = sort keys %profile_help;
 } else {
  @profiles = split /,/, $profile;
 }
}
else {
 @profiles = ();
}

# --exclude-profile: remove named profiles from the active list.
if ($exclude_profile && @profiles) {
 my %excl = map { lc($_) => 1 } split /,/, $exclude_profile;
 @profiles = grep { !$excl{lc($_)} } @profiles;
}


# =============================================
# INCIDENT MODE
# Self-contained comprehensive capture: health, profiles, services, then trace.
# =============================================
if ($incident_mode) {
 @profiles = sort keys %profile_help;
 $log      = 1;

 say_out "\n" . ("=" x 50) . "\n";
 say_out "[INCIDENT MODE] Comprehensive 60-second capture\n";
 say_out(("=" x 50) . "\n");
 say_out "All profiles active | Auto-logging enabled\n";
 say_out sprintf("Targeting top %d PIDs per profile (use --top=N to change)\n\n", $top_n);

 # --- Server health ---
 my $im_health   = check_system_health();
 my $im_critical = print_system_health($im_health);

 if ($im_critical) {
  say_out "[!] Critical metrics detected above -- extended detail will be written to log.\n\n";
 }

 # --- Profile status ---
 say_out "PROFILE STATUS\n";
 say_out "=====================================\n";
 for my $p (sort keys %profile_help) {
  my $pstat;
  if ($p eq 'php') {
   my @php = `pgrep -f php 2>/dev/null`; chomp @php;
   $pstat = @php ? sprintf("ACTIVE (%d process(es))", scalar @php)
                 : "INCLUDED (no php processes found)";
  }
  elsif ($p eq 'mysql') {
   my @mysql = `pgrep -x mysqld 2>/dev/null`; chomp @mysql;
   $pstat = @mysql ? "ACTIVE (mysqld running)"
                   : "INCLUDED (mysqld not found)";
  }
  elsif ($p eq 'user') {
   $pstat = $user ? "ACTIVE (--user=$user)"
                  : sprintf("ACTIVE (all users, top %d by CPU)", $top_n);
  }
  else {
   $pstat = sprintf("ACTIVE (top %d by CPU)", $top_n);
  }
  say_out sprintf("  %-10s %s\n", $p, $pstat);
 }
 say_out "\n";

 # --- Service status ---
 say_out "SERVICE STATUS\n";
 say_out "=====================================\n";
 my $_self_pid = $$; my $_par_pid = getppid();
 for my $svc (@supported_services) {
  my @spids = `pgrep -x $svc 2>/dev/null`; chomp @spids;
  @spids = grep { $_ != $_self_pid && $_ != $_par_pid } @spids;
  unless (@spids) {
   @spids = `pgrep -f "\\b$svc\\b" 2>/dev/null`; chomp @spids;
   @spids = grep { $_ != $_self_pid && $_ != $_par_pid } @spids;
  }
  my $proc_word = scalar(@spids) == 1 ? "process" : "processes";
  say_out sprintf("  %-15s %s\n", $svc,
                  @spids ? c_green(sprintf("RUNNING    (%d %s)", scalar @spids, $proc_word))
                         : c_red("NOT RUNNING"));
 }
 say_out "\n";
}

# =============================================
# AUTO-PROFILE
# Detects relevant profiles from running services.
# Merges with any explicitly specified profiles.
# =============================================
if ($auto_profile) {
 my @detected = detect_auto_profiles();
 my %seen     = map { $_ => 1 } @profiles;
 for my $p (@detected) {
  push @profiles, $p unless $seen{$p}++;
 }
 say_out "Using profiles: " . join(", ", @profiles) . "\n\n";
}

# =============================================
# PROFILE-CHECK (exit after checking)
# =============================================
if ($profile_check) {
 my @to_check = @profiles ? @profiles : sort keys %profile_help;
 check_profiles(@to_check);
 exit 0;
}

# =============================================
# GLOBAL RUNTIME DATA (re-initialized after mode flags are resolved)
# =============================================
$status_mode = ($status || $incident_mode) ? 1 : 0;


# =============================================
# INPUT FLAGS / -p PASSTHROUGH
# =============================================
my @original_argv = @ARGV;

for (my $i = 0; $i <= $#original_argv; $i++) {
 if ($original_argv[$i] eq "-p") {
  my $next = $original_argv[$i+1];
  if (defined $next && $next =~ /^\d+$/) {
   $pid_filter = $next;
   splice(@original_argv, $i, 2);
   last;
  } else {
   print "\nInvalid usage of -p (expected numeric PID)\n\n";
   exit 1;
  }
 }
}


# =============================================
# SCRIPT FLAG VALIDATION
# =============================================
unless ($help) {

 my $profile_used = grep { /^--profile/ } @raw_argv;
 my $service_used = grep { /^--service/ } @raw_argv;
 my $user_used    = grep { /^--user/    } @raw_argv;

 if ($profile_used) {
  if (!defined $profile || $profile eq "") {
   print "\n--profile requires a value\n\n";
   print "Valid: " . join(", ", sort keys %profile_help) . "\n\n";
   exit 1;
  }
  for my $p (@profiles) {
   unless (exists $profile_help{$p}) {
    print "\nInvalid profile: $p\n\n";
    print "Valid: " . join(", ", sort keys %profile_help) . "\n\n";
    exit 1;
   }
  }
  # --profile=user without --user is valid: traces top-N across all users
 }

 if ($user_used) {
  if (!defined $user || $user eq "") {
   print "\n--user requires a value\n\n";
   print "Example: smartstrace --user=root\n\n";
   exit 1;
  }
 }

 if ($service_used) {
  if (!defined $service || $service eq "" || $service =~ /^-/) {
   print "\n--service requires a value\n\n";
   print "Available services:\n  @supported_services\n\n";
   print "Example: smartstrace --service=httpd\n\n";
   exit 1;
  }
 }

 # quick and run are mutually exclusive (quick sets a short timeout, run removes it)
 if ($quick && $run) {
  print "\nWarning: --quick and --run are mutually exclusive; --run takes precedence\n\n";
  $quick = 0;
 }

 # --sum-logs is a standalone mode; it reads existing logs and cannot be combined
 # with live-tracing flags.
 if ($sum_logs) {
  my @operational = grep {
   /^--(run|status|quick|incident-mode|profile|profile-check|auto-profile|
       service|user|pid|log|report|json-only|json-stream|segs|csf|similar|
       watch|alert-errors|alert-cpu|top|cpu|min-errors|exclude-profile|
       context|context-only|no-color|change-log|info)/x
  } @raw_argv;
  if (@operational) {
   print "\n--sum-logs is a standalone flag and cannot be combined with operational flags.\n";
   print "  Usage: smartstrace --sum-logs=/path/to/logdir\n\n";
   print "Flags provided that are not compatible: " . join(", ", @operational) . "\n\n";
   exit 1;
  }
 }

 # --info is a standalone mode; combining it with operational flags is not meaningful.
 # --help is the only permitted companion (for contextual inline help).
 if ($info) {
  my @operational = grep {
   /^--(run|status|quick|incident-mode|profile|profile-check|auto-profile|
       service|user|pid|log|report|json-only|json-stream|segs|csf|similar|
       watch|alert-errors|alert-cpu|top|cpu|min-errors|exclude-profile|
       context|context-only|no-color|change-log)/x
  } @raw_argv;
  if (@operational) {
   print "\n--info is a standalone flag and cannot be combined with operational flags.\n";
   print "  Permitted: smartstrace --info\n";
   print "             smartstrace --info --help\n\n";
   print "Flags provided that are not compatible: " . join(", ", @operational) . "\n\n";
   exit 1;
  }
 }
}


# =============================================
# PROFILE BEHAVIOR (strace args from profile)
# =============================================
if (@profiles == 1 && $profiles[0] eq "network") {
 push @original_argv, "-e", "trace=network";
 push @original_argv, "-Ttt" unless grep { $_ =~ /-T/ } @original_argv;
 push @original_argv, "-ff"  unless grep { $_ eq "-ff" } @original_argv;
 $status    = 1 unless $status;
 $status_mode = 1;
}


# =============================================
# PARSE STRACE FLAGS
# =============================================

for (my $i = 0; $i <= $#original_argv; $i++) {
 my $arg = $original_argv[$i];
 if ($arg =~ /^-[^-]/) {
  push @strace_extra, $arg;
  if ($arg =~ /^-(e|o|s)$/) {
   my $next = $original_argv[$i+1];
   if (defined $next && $next !~ /^-/) {
    push @strace_extra, $next;
    $i++;
   } else {
    print "\nInvalid usage of $arg (missing value)\n\n";
    exit 1;
   }
  }
 }
}


# =============================================
# INVALID LONG FLAG DETECTION (with suggestions)
# =============================================
unless ($help) {

 my %valid_long = map { $_ => 1 } qw(
  run status profile service user log change-log full help
  quick json-only json-stream profile-check auto-profile incident-mode
  segs csf similar report pid top cpu alert-errors alert-cpu
  watch watch-cooldown min-errors no-color exclude-profile
  context context-only info sum-logs
 );

 # Profile names that users commonly pass as bare flags (e.g. --network instead of --profile=network)
 my %known_profiles = map { $_ => 1 } qw(network php io mysql user fpm nginx redis node cron);

 my @bad_flags;

 for my $arg (@raw_argv) {
  next unless $arg =~ /^--([A-Za-z0-9][A-Za-z0-9\-]*)/;
  my $flag = $1;
  $flag =~ s/=.*$//;          # strip any =value portion
  next if $valid_long{$flag};
  push @bad_flags, $flag;
 }

 if (@bad_flags) {
  print "\n";

  for my $flag (@bad_flags) {
   print "Unknown flag: --$flag\n";

   # Special case: exact match to a profile name
   if ($known_profiles{$flag}) {
    print "  Did you mean: --profile=$flag\n\n";
    next;
   }

   # Special case: looks like a profile typo (starts with "prof")
   if ($flag =~ /^prof/i) {
    print "  Did you mean: --profile=<name>   (network | php | io | mysql | user)\n";
    print "            or: --profile-check\n\n";
    next;
   }

   # Special case: looks like a json flag (starts with "json" or "js")
   if ($flag =~ /^js/i) {
    print "  Did you mean: --json-only   (single JSON blob on exit)\n";
    print "            or: --json-stream (NDJSON per-event output)\n\n";
    next;
   }

   # Special case: looks like alert flag (starts with "alert")
   if ($flag =~ /^alert/i) {
    print "  Did you mean: --alert-errors=N   (alert when error count exceeds N)\n";
    print "            or: --alert-cpu=N      (alert when CPU% exceeds N)\n\n";
    next;
   }

   # Special case: looks like incident-mode (starts with "inc")
   if ($flag =~ /^inc/i) {
    print "  Did you mean: --incident-mode\n\n";
    next;
   }

   # General case: find the closest valid flag by Levenshtein distance
   my $best_flag = "";
   my $best_dist = 999;
   for my $valid (sort keys %valid_long) {
    my $d = levenshtein($flag, $valid);
    if ($d < $best_dist) {
     $best_dist = $d;
     $best_flag = $valid;
    }
   }

   # Also check against profile names in case they meant --profile=<name>
   my $best_profile = "";
   my $best_pdist   = 999;
   for my $p (sort keys %known_profiles) {
    my $d = levenshtein($flag, $p);
    if ($d < $best_pdist) {
     $best_pdist = $d;
     $best_profile = $p;
    }
   }

   if ($best_pdist < $best_dist && $best_pdist <= 3) {
    print "  Did you mean: --profile=$best_profile\n\n";
   } elsif ($best_dist <= 4 && $best_flag) {
    print "  Did you mean: --$best_flag\n\n";
   } else {
    print "  Run --help to see all valid flags.\n\n";
   }
  }

  print "Aborting. Correct the flag(s) above and try again.\n\n";
  exit 1;
 }
}


# =============================================
# SERVICE VALIDATION
# Step 1: name check -- must be a supported service.
# Step 2: running check -- warn if the service has no active PIDs.
# PIDs are re-resolved fresh each loop iteration.
# =============================================
if ($service && !$help) {
 my @services = split /,/, $service;

 # Step 1: name validation
 my @invalid;
 for my $svc (@services) {
  unless (grep { $_ eq $svc } @supported_services) {
   push @invalid, $svc;
  }
 }
 if (@invalid) {
  print "\nSERVICE ERROR\n\n";
  print "Invalid service: @invalid\n\n";
  print "Available services:\n  @supported_services\n\n";
  exit 1;
 }

 # Step 2: running check -- warn but do not abort
 my @not_running;
 my $my_pid  = $$;
 my $par_pid = getppid();
 for my $svc (@services) {
  my @spids = `pgrep -x $svc 2>/dev/null`;
  chomp @spids;
  @spids = grep { $_ != $my_pid && $_ != $par_pid } @spids;
  unless (@spids) {
   @spids = `pgrep -f "\\b$svc\\b" 2>/dev/null`;
   chomp @spids;
   @spids = grep { $_ != $my_pid && $_ != $par_pid } @spids;
  }
  push @not_running, $svc unless @spids;
 }
 if (@not_running) {
  print "\nWarning: the following service(s) do not appear to be running:\n";
  print "  " . join(", ", @not_running) . "\n\n";
  print "Tracing will proceed but no processes may be found for these services.\n\n";
 }
}


# =============================================
# PROFILE STRACE ARGS
# (computed after @strace_extra is finalized)
# =============================================
if (@profiles && !grep { /^-e$/ } @strace_extra) {
 @profile_strace_args = get_profile_strace_args(@profiles);
}

# =============================================
# DEFAULT STRING SIZE
# strace default (-s32) truncates paths before they are useful.
# We default to -s256 which covers virtually all real-world paths.
# Overridden if the user has already passed their own -s flag.
# =============================================
my @default_str_size = ();
unless (grep { /^-s\d+$/ || ($_ eq '-s') } @strace_extra) {
 @default_str_size = ("-s", "256");
}

# =============================================
# RUNTIME STRACE VALIDATION
# =============================================
unless ($help) {
 if (@strace_extra && !$status_mode) {
  for (my $i = 0; $i <= $#strace_extra; $i++) {
   my $arg = $strace_extra[$i];
   next unless $arg =~ /^-/;
   if ($arg =~ /^-(e|o|s)$/) {
    my $next = $strace_extra[$i+1];
    if (!defined $next || $next =~ /^-/) {
     print "\nInvalid usage of $arg (missing value)\n\n";
     exit 1;
    }
    $i++;
    next;
   }
   for my $f (parse_flags($arg)) {
    my ($flag,undef,$valid) = @$f;
    unless ($valid && exists $strace_flag_help{$flag}) {
     print "\nInvalid strace flag: -$flag\n\n";
     print "Valid strace flags:\n";
     print "-------------------------------------\n";
     for my $k (sort keys %strace_flag_help) {
      printf "  -%-9s %s\n", $k, $strace_flag_help{$k};
     }
     print "\n";
     exit 1;
    }
   }
  }
 }
}


# =============================================
# WRITE LOG
# =============================================
sub write_log {
 return unless $log;
 return if $log_written;

 my $timestamp = time();

 unless ($log_file) {
  my ($dir, $filename) = make_log_path($timestamp);

  # Create directory tree one component at a time
  my $path = "";
  for my $part (split m{/}, $dir) {
   next unless $part;
   $path .= "/$part";
   mkdir $path unless -d $path;
  }

  if (-d $dir && -w $dir) {
   $log_file = "$dir/$filename";
  } else {
   # Fall back to current directory
   $log_file = "$filename.log";
  }
 }

 open(my $lf, ">", $log_file) or do {
  print "Failed to write log: $log_file\n";
  return;
 };

 my @lt   = localtime($timestamp);
 my $date = sprintf "%04d-%02d-%02d %02d:%02d:%02d",
            $lt[5]+1900, $lt[4]+1, $lt[3], $lt[2], $lt[1], $lt[0];

 print $lf "smartstrace v$VERSION\n";
 print $lf "Run date : $date\n";
 print $lf "Profiles : " . (@profiles ? join(", ", @profiles) : "none") . "\n";
 print $lf "=====================================\n\n";

 # Only log PIDs that produced errors.
 my @error_pids = sort grep { ($pid_errors{$_}->{total} // 0) > 0 } keys %pid_errors;

 if (@error_pids) {

  print $lf "ERROR DETAIL\n";
  print $lf "-------------------------------------\n";

  for my $pid (@error_pids) {
   my $cmd       = $pid_errors{$pid}->{cmd} // "";
   my $err_total = $pid_errors{$pid}->{total};
   my $conf      = calc_confidence($err_total);

   print $lf "\n[PID $pid]" . ($cmd ? "  ($cmd)" : "") . "\n";
   print $lf "  Total Errors : $err_total\n";
   print $lf "  Confidence   : $conf%\n";

   # Process stats (captured at selection time)
   if (defined $pid_cpu{$pid}) {
    my $cpu_str = sprintf "%.1f%%", $pid_cpu{$pid};
    $cpu_str .= "  [HIGH]" if $pid_cpu{$pid} >= $cpu_threshold;
    print $lf "  CPU Usage    : $cpu_str\n";
   }
   if (defined $pid_mem{$pid} || defined $pid_rss{$pid}) {
    my $mem_str = defined $pid_mem{$pid} ? sprintf("%.1f%%", $pid_mem{$pid}) : "";
    if (defined $pid_rss{$pid}) {
     my $r = $pid_rss{$pid};
     my $rss_fmt = $r >= 1048576 ? sprintf("%.1f GB", $r/1048576)
                 : $r >= 1024    ? sprintf("%.1f MB", $r/1024)
                 :                 sprintf("%d KB",   $r);
     $mem_str .= $mem_str ? "  ($rss_fmt RSS)" : "$rss_fmt RSS";
    }
    print $lf "  Memory       : $mem_str\n";
   }
   if (defined $pid_etimes{$pid}) {
    my $started = strftime("%Y-%m-%d %H:%M:%S", localtime(time() - $pid_etimes{$pid}));
    print $lf "  Started      : $started\n";
    print $lf "  Running for  : " . format_elapsed($pid_etimes{$pid}) . "\n";
   }

   # Per-error-type breakdown with cause, extracted paths/addrs, and hints.
   for my $e (sort keys %{$pid_errors{$pid}->{errors}}) {
    my $edata = $pid_errors{$pid}->{errors}{$e};
    printf $lf "  %-15s %d  --  %s\n",
           $e . ":",
           $edata->{count},
           ($error_causes{$e} // "Unknown");

    # Burst annotation
    if (my @burst = detect_burst($edata->{timestamps})) {
     my ($n, $t) = @burst;
     my @lt = localtime($t);
     my $ts = sprintf "%02d:%02d:%02d", $lt[2], $lt[1], $lt[0];
     printf $lf "    [BURST: %d errors in <1s at %s]\n", $n, $ts;
    }

    # Extracted paths
    if (my $paths = $edata->{paths}) {
     my @sorted = sort { $paths->{$b} <=> $paths->{$a} } keys %$paths;
     for my $p (@sorted) {
      printf $lf "    %-55s (%d×)\n", $p, $paths->{$p};
      my ($short, $detail) = path_hint($p);
      if ($short) {
       print $lf "    [!] $short\n";
       print $lf "        -> $detail\n";
      }
     }
    }

    # Extracted addresses
    if (my $addrs = $edata->{addrs}) {
     my @sorted = sort { $addrs->{$b} <=> $addrs->{$a} } keys %$addrs;
     for my $a (@sorted) {
      printf $lf "    %-55s (%d×)\n", $a, $addrs->{$a};
      my ($port) = $a =~ /:(\d+)$/;
      my ($svc, $cmd) = port_hint($port);
      if ($svc) {
       print $lf "    [!] $svc not responding\n";
       print $lf "        -> $cmd\n";
      }
     }
    }
   }

   # Top syscalls observed for this PID.
   if ($syscall_count{$pid}) {
    my @top = sort { $syscall_count{$pid}{$b} <=> $syscall_count{$pid}{$a} }
                  keys %{$syscall_count{$pid}};
    @top = @top[0..9] if @top > 10;
    print $lf "  Top syscalls : " . join(", ", @top) . "\n";
   }
  }

  print $lf "\n";

  # Extended context for high-error PIDs -- log only, not shown on terminal
  my @critical_pids = grep { ($pid_errors{$_}->{total} // 0) >= 50 } @error_pids;
  if (@critical_pids) {
   print $lf "CRITICAL PROCESS DETAIL\n";
   print $lf "-------------------------------------\n";
   print $lf "(PIDs with 50+ errors -- extended context)\n\n";
   for my $pid (@critical_pids) {
    my $cmd = $pid_errors{$pid}->{cmd} // do {
     my $c = `ps -o comm= -p $pid 2>/dev/null`; chomp $c; $c;
    };
    my $usr = `ps -o user= -p $pid 2>/dev/null`;
    chomp($usr);
    my $err_total = $pid_errors{$pid}->{total};
    print $lf "[PID $pid]  cmd=" . ($cmd || "unknown")
            . "  user=" . ($usr || "unknown")
            . "  errors=$err_total\n";
    my $errs = $pid_errors{$pid}->{errors} // {};
    for my $e (sort keys %$errs) {
     my $edata = $errs->{$e};
     my $count = $edata->{count} // 0;
     my $cause = $error_causes{$e} // "Unknown";
     printf $lf "  %s (%d occurrence%s) -- %s\n",
            $e, $count, ($count == 1 ? "" : "s"), $cause;
     if (my $blocks = $edata->{blocks}) {
      my $shown = 0;
      for my $block (@$blocks) {
       $shown++;
       print $lf "  --- occurrence $shown ---\n";
       # All lines in the block; last line is the error line itself.
       # Preceding lines are the calling context.
       for my $i (0 .. $#$block) {
        my $prefix = ($i == $#$block) ? "  > " : "    ";
        print $lf "$prefix$block->[$i]\n";
       }
      }
      if ($count > $shown) {
       printf $lf "  ... (%d more unique occurrence%s not captured)\n",
              $count - $shown, ($count - $shown == 1 ? "" : "s");
      }
     }
     print $lf "\n";
    }
    # Path/port-aware recommendations
    my $rec_count = 0;
    for my $e (qw(ENOENT EACCES ECONNREFUSED ETIMEDOUT SIGSEGV EMFILE ENOSPC EADDRINUSE)) {
     next unless exists $errs->{$e} && ($errs->{$e}{count} // 0) > 0;
     my $edata = $errs->{$e};
     # Emit specific hints from extracted paths
     if (my $paths = $edata->{paths}) {
      my %seen_hints;
      for my $p (sort { $paths->{$b} <=> $paths->{$a} } keys %$paths) {
       my ($short, $detail) = path_hint($p);
       next unless $short;
       next if $seen_hints{$short}++;
       print $lf "  [!] $short\n";
       print $lf "      -> $detail\n";
       $rec_count++;
      }
     }
     # Emit specific hints from extracted addresses
     if (my $addrs = $edata->{addrs}) {
      my %seen_hints;
      for my $a (sort { $addrs->{$b} <=> $addrs->{$a} } keys %$addrs) {
       my ($port) = $a =~ /:(\d+)$/;
       my ($svc, $cmd) = port_hint($port);
       next unless $svc;
       next if $seen_hints{$svc}++;
       print $lf "  [!] $svc not responding  ($a)\n";
       print $lf "      -> $cmd\n";
       $rec_count++;
      }
     }
     # Generic fallbacks when no specific pattern matched
     unless ($rec_count) {
      if    ($e eq 'EACCES')       { print $lf "  Recommendation: Check file/directory ownership and permissions\n"; $rec_count++; }
      elsif ($e eq 'ECONNREFUSED') { print $lf "  Recommendation: Verify target service is running and not blocked by firewall\n"; $rec_count++; }
      elsif ($e eq 'ENOENT')       { print $lf "  Recommendation: Check config paths and symlinks\n"; $rec_count++; }
      elsif ($e eq 'ETIMEDOUT')    { print $lf "  Recommendation: Check network reachability and DNS resolution\n"; $rec_count++; }
      elsif ($e eq 'SIGSEGV')      { print $lf "  Recommendation: Review for crashes; run with --segs for detail\n"; $rec_count++; }
      elsif ($e eq 'EMFILE')       { print $lf "  Recommendation: File descriptor limit hit -- check ulimit -n and /proc/PID/limits; consider raising nofile in /etc/security/limits.conf\n"; $rec_count++; }
      elsif ($e eq 'ENOSPC')       { print $lf "  Recommendation: Disk full -- run: df -h; du -sh /* 2>/dev/null | sort -rh | head\n"; $rec_count++; }
      elsif ($e eq 'EADDRINUSE')   { print $lf "  Recommendation: Port already bound -- check: ss -tlnp | grep PORT to find conflicting process\n"; $rec_count++; }
     }
    }
    print $lf "\n";
   }
  }

 } else {
  print $lf "No errors detected during this run.\n\n";
 }

 # Shared failure correlation
 my $shared = find_shared_failures();
 my @sp = sort { scalar(@{$shared->{paths}{$b}}) <=> scalar(@{$shared->{paths}{$a}}) }
          keys %{$shared->{paths}};
 my @sa = sort { scalar(@{$shared->{addrs}{$b}}) <=> scalar(@{$shared->{addrs}{$a}}) }
          keys %{$shared->{addrs}};
 if (@sp || @sa) {
  print $lf "SHARED FAILURES  (same target seen in 2+ processes)\n";
  print $lf "-------------------------------------\n";
  for my $t (@sp) {
   my $pids = $shared->{paths}{$t};
   my $cmds = join(", ", map { $pid_errors{$_}->{cmd} // $_ } @$pids);
   printf $lf "  %-50s  %d PIDs  (%s)\n", $t, scalar(@$pids), $cmds;
   my ($short, $detail) = path_hint($t);
   if ($short) { print $lf "    [!] $short\n    -> $detail\n"; }
  }
  for my $t (@sa) {
   my $pids = $shared->{addrs}{$t};
   my $cmds = join(", ", map { $pid_errors{$_}->{cmd} // $_ } @$pids);
   printf $lf "  %-50s  %d PIDs  (%s)\n", $t, scalar(@$pids), $cmds;
   my ($port) = $t =~ /:(\d+)$/;
   my ($svc, $cmd) = port_hint($port);
   if ($svc) { print $lf "    [!] $svc not responding\n    -> $cmd\n"; }
  }
  print $lf "\n";
 }

 print $lf "GLOBAL SUMMARY\n";
 print $lf "-------------------------------------\n";
 print $lf "Processes Traced  : $total_traced\n";
 print $lf "Errors Found      : $total_errors\n";
 if ($total_errors) {
  print $lf "Overall Confidence: " . calc_confidence($total_errors) . "%\n";
 }
 if ($d_state_skipped) {
  print $lf "D-State Skipped   : $d_state_skipped process(es) -- uninterruptible sleep, cannot be traced\n";
 }
 if ($ptrace_denied) {
  print $lf "Attach Denied     : $ptrace_denied process(es) -- Operation not permitted\n";
  for my $hint (ptrace_denial_hints()) {
   print $lf "                    $hint\n";
  }
 }
 print $lf "\n";

 close $lf;
 $log_written = 1;
 print "Log written: $log_file\n";
}


# =============================================
# FINISH (shared cleanup -- called by SIGINT and normal exit)
# FIX #8: named sub so both the signal handler and the normal
# end-of-run path invoke the same cleanup code reliably.
# =============================================
# Returns a list of targeted hint strings explaining why ptrace was denied,
# taking into account ptrace_scope, SELinux, AppArmor, and CloudLinux.
# Returns (short_hint, detail_hint) for a filesystem path, or () if no match.
sub path_hint {
 my ($path) = @_;
 for my $entry (@path_hints) {
  my ($pat, $short, $detail) = @$entry;
  return ($short, $detail) if $path =~ $pat;
 }
 return ();
}

# Returns (service_name, check_command) for a port number, or () if unknown.
sub port_hint {
 my ($port) = @_;
 return () unless defined $port && exists $port_hints{$port};
 return @{$port_hints{$port}};
}

# Detect error bursts: returns (max_in_1s, epoch_of_burst) if 5+ errors occurred
# within a single second window; otherwise returns empty list.
sub detect_burst {
 my ($ts_aref) = @_;
 return () unless $ts_aref && @$ts_aref >= 5;
 my @ts = sort { $a <=> $b } @$ts_aref;
 my ($max_burst, $burst_time) = (0, 0);
 for my $i (0 .. $#ts) {
  my $cutoff = $ts[$i] + 1;
  my $count  = 0;
  for my $j ($i .. $#ts) { last if $ts[$j] > $cutoff; $count++; }
  if ($count > $max_burst) { $max_burst = $count; $burst_time = $ts[$i]; }
 }
 return ($max_burst, $burst_time) if $max_burst >= 5;
 return ();
}

# Format extracted paths or addresses under an error line in terminal output.
# $edata    = $pid_errors{$pid}{errors}{$err}
# $err      = error name (ENOENT etc.)
# $indent   = leading spaces string
# $max      = max entries to show (default 3)
sub show_error_extracted {
 my ($edata, $err, $indent, $max) = @_;
 $max //= 3;

 # Burst annotation
 if (my @burst = detect_burst($edata->{timestamps})) {
  my ($n, $t) = @burst;
  my @lt = localtime($t);
  my $ts = sprintf "%02d:%02d:%02d", $lt[2], $lt[1], $lt[0];
  say_out sprintf("%s    [BURST: %d errors in <1s at %s]\n", $indent, $n, $ts);
 }

 # Paths (ENOENT / EACCES / ENOSPC)
 if (my $paths = $edata->{paths}) {
  my @sorted = sort { $paths->{$b} <=> $paths->{$a} } keys %$paths;
  my $shown  = 0;
  for my $p (@sorted) {
   last if $shown >= $max;
   say_out sprintf("%s    %-55s (%d×)\n", $indent, $p, $paths->{$p});
   my ($short, $detail) = path_hint($p);
   if ($short) {
    say_out "$indent    [!] $short\n";
    say_out "$indent        -> $detail\n";
   }
   $shown++;
  }
  if (@sorted > $max) {
   say_out sprintf("%s    … and %d more path(s)\n", $indent, scalar(@sorted) - $max);
  }
 }

 # Addresses (ECONNREFUSED / ETIMEDOUT / EADDRINUSE)
 if (my $addrs = $edata->{addrs}) {
  my @sorted = sort { $addrs->{$b} <=> $addrs->{$a} } keys %$addrs;
  my $shown  = 0;
  for my $a (@sorted) {
   last if $shown >= $max;
   say_out sprintf("%s    %-55s (%d×)\n", $indent, $a, $addrs->{$a});
   my ($port) = $a =~ /:(\d+)$/;
   my ($svc, $cmd) = port_hint($port);
   if ($svc) {
    say_out "$indent    [!] $svc not responding\n";
    say_out "$indent        -> $cmd\n";
   }
   $shown++;
  }
  if (@sorted > $max) {
   say_out sprintf("%s    ... and %d more address(es)\n", $indent, scalar(@sorted) - $max);
  }
 }

 # Inline hints for new error types with no path/addr extraction
 if ($err eq 'EMFILE') {
  say_out "$indent    [!] File descriptor limit hit\n";
  say_out "$indent        -> ulimit -n; cat /proc/$$/limits; check /etc/security/limits.conf\n";
 } elsif ($err eq 'ENOSPC' && !$edata->{paths}) {
  say_out "$indent    [!] Disk full\n";
  say_out "$indent        -> df -h; du -sh /* 2>/dev/null | sort -rh | head\n";
 } elsif ($err eq 'EADDRINUSE' && !$edata->{addrs}) {
  say_out "$indent    [!] Port conflict -- another process holds this address\n";
  say_out "$indent        -> ss -tlnp\n";
 }
}

# After tracing completes, find paths/addresses seen across 2+ distinct PIDs.
# Returns hashref: { paths => { target => [pid,...] }, addrs => { target => [pid,...] } }
sub find_shared_failures {
 my %shared = (paths => {}, addrs => {});
 for my $pid (keys %pid_errors) {
  for my $err (keys %{$pid_errors{$pid}->{errors} // {}}) {
   for my $t (keys %{$pid_errors{$pid}->{errors}{$err}->{paths} // {}}) {
    push @{$shared{paths}{$t}}, $pid;
   }
   for my $t (keys %{$pid_errors{$pid}->{errors}{$err}->{addrs} // {}}) {
    push @{$shared{addrs}{$t}}, $pid;
   }
  }
 }
 # Deduplicate PIDs per target and keep only those with 2+ distinct PIDs
 for my $type (qw(paths addrs)) {
  for my $target (keys %{$shared{$type}}) {
   my %seen;
   @{$shared{$type}{$target}} = grep { !$seen{$_}++ } @{$shared{$type}{$target}};
   delete $shared{$type}{$target} if @{$shared{$type}{$target}} < 2;
  }
 }
 return \%shared;
}

sub ptrace_denial_hints {
 my @hints;

 # Read ptrace_scope
 my $scope = -1;
 if (open(my $f, "<", "/proc/sys/kernel/yama/ptrace_scope")) {
  chomp(my $val = <$f>); close $f;
  $scope = $val + 0;
 }

 if ($scope == 0) {
  push @hints,
   "ptrace_scope is already 0 -- another policy is blocking ptrace:",
   "  - SELinux or AppArmor may be denying ptrace regardless of ptrace_scope",
   "  - CloudLinux kernel patches may protect certain system processes",
   "  - The target process may have cleared the dumpable flag (PR_SET_DUMPABLE)";
 } elsif ($scope == 1) {
  push @hints, "Lower ptrace scope: echo 0 > /proc/sys/kernel/yama/ptrace_scope";
 } elsif ($scope >= 2) {
  push @hints,
   "ptrace_scope=$scope -- only root can trace, and only non-protected processes",
   "  Lower ptrace scope: echo 0 > /proc/sys/kernel/yama/ptrace_scope";
 } else {
  push @hints, "Run as root or set ptrace_scope=0 to trace those PIDs";
 }

 # SELinux
 my $selinux = do {
  if (open(my $f, "<", "/sys/fs/selinux/enforce")) {
   chomp(my $v = <$f>); close $f; $v;
  } else { "" }
 };
 if ($selinux eq "1") {
  push @hints,
   "SELinux is Enforcing -- it may be blocking ptrace independently of ptrace_scope",
   "  Check for AVC denials: ausearch -m avc -ts recent | grep ptrace";
 }

 # AppArmor
 if (-d "/sys/kernel/security/apparmor") {
  my $aa_mode = "";
  if (open(my $f, "<", "/sys/kernel/security/apparmor/profiles")) {
   close $f; $aa_mode = "active";
  }
  push @hints, "AppArmor is active -- a loaded profile may restrict ptrace"
   if $aa_mode;
 }

 # CloudLinux
 if (-f "/etc/cloudlinux-release" || -d "/opt/cloudlinux") {
  push @hints,
   "CloudLinux detected -- system processes protected by CL kernel patches cannot",
   "  be traced even as root; this is expected for cPanel/WHM infrastructure processes";
 }

 return @hints;
}

# Format elapsed seconds into a human-readable string: "3d 2h 15m 4s"
sub format_elapsed {
 my ($s) = @_;
 return "unknown" unless defined $s && $s =~ /^\d+$/;
 my $d = int($s / 86400); $s %= 86400;
 my $h = int($s / 3600);  $s %= 3600;
 my $m = int($s / 60);    $s %= 60;
 my @parts;
 push @parts, "${d}d" if $d;
 push @parts, "${h}h" if $h || $d;
 push @parts, "${m}m" if $m || $h || $d;
 push @parts, "${s}s";
 return join " ", @parts;
}

# Emit process stats (CPU, memory, start time, uptime) and a recommendation
# block when CPU is high.  Replaces the old process_stats_annotation() sub and is used
# by all three display paths in finish() so the format is consistent.
sub process_stats_annotation {
 my ($pid, $indent) = @_;
 $indent //= "  ";

 my $cpu    = $pid_cpu{$pid};
 my $mem    = $pid_mem{$pid};
 my $rss    = $pid_rss{$pid};
 my $etimes = $pid_etimes{$pid};

 # CPU
 if (defined $cpu) {
  if ($cpu >= $cpu_threshold) {
   say_out sprintf("%sCPU Usage    : %.1f%%  [HIGH]\n", $indent, $cpu);
   say_out $indent . "[!] This process is consuming significant CPU.\n";
   say_out $indent . "    Investigate further with smartstrace:\n";
   say_out $indent . "      smartstrace --pid=$pid --run\n";
   say_out $indent . "      smartstrace --pid=$pid --run -T -tt       (with timing)\n";
   say_out $indent . "      smartstrace --pid=$pid --run -ff          (follow forks)\n";
   say_out $indent . "      smartstrace --pid=$pid --alert-errors=10  (live alerts)\n";
  } else {
   say_out sprintf("%sCPU Usage    : %.1f%%\n", $indent, $cpu);
  }
 }

 # Memory
 if (defined $mem || defined $rss) {
  my $mem_str = defined $mem ? sprintf("%.1f%%", $mem) : "";
  if (defined $rss) {
   my $rss_str = $rss >= 1048576 ? sprintf("%.1f GB", $rss / 1048576)
               : $rss >= 1024    ? sprintf("%.1f MB", $rss / 1024)
               :                   sprintf("%d KB",   $rss);
   $mem_str .= $mem_str ? "  ($rss_str RSS)" : $rss_str . " RSS";
  }
  say_out sprintf("%sMemory       : %s\n", $indent, $mem_str);
 }

 # Uptime and start time
 if (defined $etimes) {
  my $started = strftime("%Y-%m-%d %H:%M:%S", localtime(time() - $etimes));
  say_out sprintf("%sStarted      : %s\n",   $indent, $started);
  say_out sprintf("%sRunning for  : %s\n",   $indent, format_elapsed($etimes));
 }
}

# =============================================
# ERROR TIMELINE
# Renders an ASCII bar chart of error density across the trace window.
# Called from finish() after PROCESS ANALYSIS when total_errors > 0.
# =============================================
sub show_error_timeline {
 # Collect all timestamps from all PIDs and error types
 my @all_ts;
 for my $pid (keys %pid_errors) {
  for my $err (keys %{$pid_errors{$pid}->{errors} // {}}) {
   my $tsa = $pid_errors{$pid}->{errors}{$err}->{timestamps};
   push @all_ts, @$tsa if $tsa;
  }
 }
 return unless @all_ts;

 my $t_start = $trace_start_time // (sort { $a <=> $b } @all_ts)[0];
 my $t_end   = $trace_end_time   // time();
 my $duration = $t_end - $t_start;
 $duration = 1 if $duration < 1;

 my $bucket_size = $duration > 20 ? int(($duration + 19) / 20) : 1;
 my $num_slots   = int(($duration + $bucket_size - 1) / $bucket_size);
 $num_slots = 1 if $num_slots < 1;

 my @buckets = (0) x $num_slots;
 for my $ts (@all_ts) {
  my $offset = $ts - $t_start;
  $offset = 0              if $offset < 0;
  $offset = $duration - 1  if $offset >= $duration;
  my $slot = int($offset / $bucket_size);
  $slot = $num_slots - 1 if $slot >= $num_slots;
  $buckets[$slot]++;
 }

 my $max_count = (sort { $b <=> $a } @buckets)[0];
 $max_count = 1 if $max_count < 1;
 my $bar_width = 40;

 say_out "\nERROR TIMELINE\n";
 say_out "=====================================\n";

 for my $i (0 .. $num_slots - 1) {
  my $count   = $buckets[$i];
  my $sec     = $i * $bucket_size;
  my $bar_len = int($bar_width * $count / $max_count);
  $bar_len = 0 if $count == 0;
  my $bar     = "#" x $bar_len;
  my $label   = $bucket_size > 1
              ? sprintf("%ds-%ds", $sec, $sec + $bucket_size - 1)
              : sprintf("%ds", $sec);
  say_out sprintf("  %-12s |%-40s  %d\n", $label, $bar, $count);
 }
 say_out sprintf("  Total duration: %ds\n", $duration);
 say_out "\n";
}


# =============================================
# RSS GROWTH TRACKING
# Compares initial vs peak RSS per PID.
# Called from finish() before GLOBAL SUMMARY.
# =============================================
sub show_rss_growth {
 my @growth_pids;
 for my $pid (keys %pid_rss_initial) {
  my $init = $pid_rss_initial{$pid} // 0;
  my $peak = $pid_rss_peak{$pid}    // $init;
  next unless $init > 0;
  my $delta  = $peak - $init;
  my $pct    = ($delta / $init) * 100;
  # Flag if growth >= 20% AND >= 5 MB (5120 KB)
  if ($pct >= 20 && $delta >= 5120) {
   push @growth_pids, { pid => $pid, init => $init, peak => $peak,
                        delta => $delta, pct => $pct };
  }
 }
 return unless @growth_pids;

 say_out "\nMEMORY GROWTH\n";
 say_out "=====================================\n";

 for my $entry (sort { $b->{delta} <=> $a->{delta} } @growth_pids) {
  my $pid   = $entry->{pid};
  my $cmd   = $pid_errors{$pid}->{cmd} // do {
   my $c = `ps -o comm= -p $pid 2>/dev/null`; chomp $c; $c;
  };
  my $init_fmt  = $entry->{init} >= 1024
                ? sprintf("%.1f MB", $entry->{init} / 1024)
                : sprintf("%d KB",   $entry->{init});
  my $peak_fmt  = $entry->{peak} >= 1024
                ? sprintf("%.1f MB", $entry->{peak} / 1024)
                : sprintf("%d KB",   $entry->{peak});
  my $delta_fmt = $entry->{delta} >= 1024
                ? sprintf("+%.1f MB", $entry->{delta} / 1024)
                : sprintf("+%d KB",   $entry->{delta});
  say_out sprintf("  PID %-7s  %-15s  %s -> %s  %s (+%.0f%%)\n",
                  $pid, ($cmd || "unknown"),
                  $init_fmt, $peak_fmt, $delta_fmt, $entry->{pct});
 }
 say_out "\n";
}


# =============================================
# PROCESS TREE AWARENESS
# Reads /proc/$pid/status to walk up the parent chain.
# =============================================
sub get_parent_chain {
 my ($pid) = @_;
 my @chain;
 my $current = $pid;
 my $levels  = 0;

 while ($levels < 4) {
  my $ppid;
  my $pname = "";
  if (open(my $sf, "<", "/proc/$current/status")) {
   while (<$sf>) {
    if (/^PPid:\s+(\d+)/)  { $ppid  = $1; }
    if (/^Name:\s+(\S+)/)  { $pname = $1; }
   }
   close $sf;
  }
  last unless defined $ppid && $ppid =~ /^\d+$/ && $ppid > 1;

  my $parent_name = "";
  if (open(my $psf, "<", "/proc/$ppid/status")) {
   while (<$psf>) {
    if (/^Name:\s+(\S+)/) { $parent_name = $1; last; }
   }
   close $psf;
  }
  push @chain, { pid => $ppid, name => $parent_name };
  $current = $ppid;
  $levels++;
  last if $ppid == 1;
 }

 return \@chain;
}

sub show_process_tree {
 my ($pid, $indent) = @_;
 $indent //= "  ";
 my $chain = get_parent_chain($pid);
 return unless $chain && @$chain;
 my $tree_str = join(" -> ", map { "$_->{name} (PID $_->{pid})" } @$chain);
 say_out sprintf("%sParent chain : %s\n", $indent, $tree_str);
}


# =============================================
# SYSCALL HOTSPOT REPORTING
# Shows top 5 syscalls by count for a given PID.
# Called from all three PROCESS ANALYSIS display paths.
# =============================================
sub show_syscall_hotspots {
 my ($pid, $duration, $indent) = @_;
 $indent   //= "  ";
 $duration //= 1;
 $duration   = 1 if $duration < 1;

 return unless $syscall_count{$pid} && %{$syscall_count{$pid}};

 my @sorted = sort { $syscall_count{$pid}{$b} <=> $syscall_count{$pid}{$a} }
              keys %{$syscall_count{$pid}};
 my $total = 0;
 $total += $syscall_count{$pid}{$_} for @sorted;

 my @top = @sorted > 5 ? @sorted[0..4] : @sorted;

 say_out sprintf("%sSyscalls     : %d total\n", $indent, $total);
 for my $sc (@top) {
  my $count = $syscall_count{$pid}{$sc};
  my $rate  = sprintf("%.1f", $count / $duration);
  say_out sprintf("%s  %-20s %5d  (%s/s)\n", $indent, $sc, $count, $rate);
 }
}


# =============================================
# CONTEXT-ONLY TERMINAL DISPLAY
# Prints captured strace context blocks for a PID directly to terminal output.
# Used when --context-only is active. Organises output under the calling PID's
# section (user / service / default grouping) — no log file required.
# Error lines are visually distinguished from surrounding context lines.
# =============================================
sub show_pid_context_terminal {
 my ($pid, $indent) = @_;
 $indent //= "  ";
 my $errs = $pid_errors{$pid}->{errors} // {};

 my $any_blocks = 0;
 for my $e (sort keys %$errs) {
  my $blocks = $errs->{$e}->{blocks};
  $any_blocks++ if $blocks && @$blocks;
 }
 return unless $any_blocks;

 say_out "${indent}STRACE CONTEXT\n";
 say_out "${indent}-------------------------------------\n";

 for my $e (sort keys %$errs) {
  my $edata  = $errs->{$e};
  my $blocks = $edata->{blocks};
  next unless $blocks && @$blocks;

  my $count  = $edata->{count} // 0;
  my $n      = scalar @$blocks;
  say_out sprintf("%s[%s]  %d occurrence%s  (%d unique block%s)\n",
                  $indent, $e,
                  $count, ($count == 1 ? "" : "s"),
                  $n,     ($n     == 1 ? "" : "s"));

  my $shown = 0;
  for my $block (@$blocks) {
   $shown++;
   say_out sprintf("%s  -- context block %d --\n", $indent, $shown);
   for my $i (0 .. $#$block) {
    if ($i == $#$block) {
     # Final line is the error line itself -- highlight it
     say_out $indent . "  > " . c_red($block->[$i]) . "\n";
    } else {
     say_out "${indent}    $block->[$i]\n";
    }
   }
  }

  if ($count > $n) {
   say_out sprintf("%s  ... (%d more occurrence%s not captured in context)\n",
                   $indent, $count - $n, ($count - $n == 1 ? "" : "s"));
  }
  say_out "\n";
 }
}


# =============================================
# CPANEL/WHM LOG CORRELATION
# Scans known cPanel log files for entries within the trace window.
# Only runs when /usr/local/cpanel or /opt/cpanel exists.
# =============================================
sub parse_log_timestamp {
 my ($line) = @_;

 # Apache/cPanel format: [Mon May 10 12:34:56.123 2026]
 if ($line =~ /\[(\w{3})\s+(\w{3})\s+(\d{1,2})\s+(\d{2}):(\d{2}):(\d{2})(?:\.\d+)?\s+(\d{4})\]/) {
  my ($wday, $mon_str, $mday, $hour, $min, $sec, $year) = ($1,$2,$3,$4,$5,$6,$7);
  my $mon = $MONTHS{$mon_str};
  return undef unless defined $mon;
  return mktime($sec+0, $min+0, $hour+0, $mday+0, $mon, $year-1900);
 }

 # Syslog format: May 10 12:34:56
 if ($line =~ /^(\w{3})\s+(\d{1,2})\s+(\d{2}):(\d{2}):(\d{2})\b/) {
  my ($mon_str, $mday, $hour, $min, $sec) = ($1,$2,$3,$4,$5);
  my $mon = $MONTHS{$mon_str};
  return undef unless defined $mon;
  my @now = localtime(time());
  return mktime($sec+0, $min+0, $hour+0, $mday+0, $mon, $now[5]);
 }

 # ISO format: 2026-05-10 12:34:56 or 2026-05-10T12:34:56
 if ($line =~ /(\d{4})-(\d{2})-(\d{2})[T ](\d{2}):(\d{2}):(\d{2})/) {
  my ($year, $mon, $mday, $hour, $min, $sec) = ($1,$2,$3,$4,$5,$6);
  return mktime($sec+0, $min+0, $hour+0, $mday+0, $mon-1, $year-1900);
 }

 return undef;
}

sub correlate_logs {
 my ($t_start, $t_end) = @_;

 return unless -d "/usr/local/cpanel" || -d "/opt/cpanel";

 my @log_sources = (
  [ "/usr/local/cpanel/logs/error_log",           "cPanel    " ],
  [ "/usr/local/apache/logs/error_log",            "Apache    " ],
  [ "/usr/local/apache/logs/suexec_log",           "Suexec    " ],
  [ "/var/log/messages",                           "Messages  " ],
  [ "/var/log/secure",                             "Secure    " ],
  [ "/usr/local/cpanel/logs/php-fpm/error.log",   "PHP-FPM   " ],
  [ "/var/log/mysql/error.log",                    "MySQL     " ],
 );

 # Add LiteSpeed log only if lshttpd is running
 {
  my $stack = $web_stack //= detect_web_stack();
  if ($stack->{litespeed}) {
   push @log_sources, [ "/usr/local/lsws/logs/error.log", "LiteSpeed " ];
  }
 }

 my $window_start = $t_start - 5;
 my $window_end   = $t_end   + 5;

 my @entries;
 my $total_found = 0;

 for my $src (@log_sources) {
  my ($path, $label) = @$src;
  next unless -r $path && -e $path;
  my @lines = `tail -n 500 $path 2>/dev/null`;
  for my $line (@lines) {
   last if $total_found >= 50;
   chomp $line;
   next if length($line) < 15;
   next if $line =~ /^\s*$/;
   next if $line =~ /^#/;
   next if $line =~ /^\s*(notice|info|debug)\b/i;
   my $ts = parse_log_timestamp($line);
   next unless defined $ts;
   next if $ts < $window_start || $ts > $window_end;
   my $display = length($line) > 120 ? substr($line, 0, 120) : $line;
   push @entries, "  [$label] $display";
   $total_found++;
  }
 }

 return unless @entries;

 say_out "\nLOG CORRELATION  (entries within trace window)\n";
 say_out "=====================================\n";
 for my $entry (@entries) {
  say_out "$entry\n";
 }
 say_out "\n";
}


sub finish {

 $trace_end_time = time();

 # Sort all error PIDs by total error count (highest first).
 my @error_pids = sort { ($pid_errors{$b}->{total} // 0) <=> ($pid_errors{$a}->{total} // 0) }
                  grep { ($pid_errors{$_}->{total} // 0) > 0 } keys %pid_errors;

 # Apply --min-errors filter before top-N (terminal only; log always gets all PIDs).
 if (defined $min_errors && $min_errors > 0) {
  @error_pids = grep { ($pid_errors{$_}->{total} // 0) >= $min_errors } @error_pids;
 }

 # Apply top-N display limit (terminal only; log always gets all PIDs).
 my $display_limit = $top_n || 5;
 my @display_pids  = @error_pids > $display_limit
                   ? @error_pids[0..$display_limit-1]
                   : @error_pids;
 my $truncated     = scalar(@error_pids) > $display_limit;

 # -------------------------------------------------------
 # PROFILE SUMMARY
 # Only printed when errors were identified. Profiles that
 # saw no errors are omitted entirely -- no noise.
 # -------------------------------------------------------
 if (@profiles && @display_pids) {
  say_out "\nPROFILE SUMMARY\n";
  say_out "=====================================\n";

  # Show profiles with zero results first (Change 13)
  for my $p (@profiles) {
   if (exists $profile_pid_count{$p} && $profile_pid_count{$p} == 0) {
    my $pgrep_desc = $p eq 'php'   ? "pgrep -f php"
                   : $p eq 'fpm'   ? "pgrep -f php-fpm"
                   : $p eq 'mysql' ? "pgrep -x mysqld"
                   : $p eq 'nginx' ? "pgrep -x nginx"
                   : $p eq 'redis' ? "pgrep -x redis-server"
                   : $p eq 'node'  ? "pgrep -x node"
                   : $p eq 'cron'  ? "pgrep -x crond"
                   :                 "pgrep";
    say_out sprintf("  [%s]  -- no processes found (%s returned 0 results)\n",
                    $p, $pgrep_desc);
   }
  }

  for my $p (@profiles) {

   # Show only PIDs that this profile actually targeted AND had any errors.
   # Using %pid_source_profiles (populated at discovery time) rather than
   # guessing profile membership from error type -- avoids showing php/mysql
   # PIDs when those services aren't running on this server.
   my @profile_error_pids = grep {
    $pid_source_profiles{$_}{$p} &&
    do {
     my $e = $pid_errors{$_}->{errors} // {};
     grep { ($e->{$_}->{count} // 0) > 0 } keys %$e;
    }
   } @display_pids;

   next unless @profile_error_pids;

   # Build syscall filter description for this profile (Change 14)
   my @pargs = get_profile_strace_args($p);
   my $filter_desc;
   if (@pargs) {
    # @pargs is like ("-e", "trace=network,file") -> extract the value
    my $trace_val = "";
    for my $i (0 .. $#pargs) {
     if ($pargs[$i] eq '-e' && defined $pargs[$i+1]) {
      $trace_val = $pargs[$i+1];
      last;
     }
    }
    $filter_desc = "(-e $trace_val)";
   } else {
    $filter_desc = "(all syscalls)";
   }

   say_out "\n[$p] $filter_desc -- " . scalar(@profile_error_pids) . " PID(s) with errors\n";

   for my $pid (@profile_error_pids) {
    my $cmd = `ps -o comm= -p $pid 2>/dev/null`;
    chomp $cmd;
    my $errs = $pid_errors{$pid}->{errors} // {};
    my @parts = map  { "$_=" . $errs->{$_}->{count} }
                grep { exists $errs->{$_} && defined $errs->{$_}->{count} }
                sort keys %$errs;
    say_out sprintf("  PID %-7s  %-15s  %s\n",
                    $pid, ($cmd || "unknown"), join("  ", @parts));
   }
  }

  say_out "\n";
 }

 # -------------------------------------------------------
 # INCIDENT MODE: USER STATUS
 # After tracing, show which users own the most errored processes.
 # Shown only in --incident-mode and only when errors were found.
 # -------------------------------------------------------
 if ($incident_mode && @error_pids) {
  say_out "USER STATUS (Error Summary)\n";
  say_out "=====================================\n";
  my %user_errors;
  for my $pid (@error_pids) {
   my $u = `ps -o user= -p $pid 2>/dev/null`;
   chomp $u;
   $u =~ s/\s+//g;
   $u ||= "unknown";
   $user_errors{$u} += $pid_errors{$pid}->{total} // 0;
  }
  my @top_users = (sort { $user_errors{$b} <=> $user_errors{$a} } keys %user_errors)[0..4];
  @top_users = grep { defined } @top_users;
  for my $u (@top_users) {
   say_out sprintf("  %-15s %d error(s)\n", $u, $user_errors{$u});
  }
  say_out "\n";
 }

 # -------------------------------------------------------
 # PROCESS ANALYSIS
 # Only PIDs with errors, limited to top-N, sorted by error count.
 # Grouped by user when --profile=user or --user is active.
 # Grouped by service when --service is active.
 # Default: list PIDs with UID shown.
 # -------------------------------------------------------
 if (@display_pids) {
  say_out "\nPROCESS ANALYSIS\n";
  say_out "=====================================\n";

  if ($truncated) {
   say_out sprintf("(Showing top %d of %d processes with errors -- use --top=N for more)\n",
                   $display_limit, scalar @error_pids);
  }

  # Determine grouping mode
  my $group_by_user    = ($user || grep { $_ eq 'user' } @profiles);
  my $group_by_service = ($service && !$group_by_user);

  if ($group_by_user) {
   # Group display PIDs by their owning user
   my %by_user;
   my @user_order;
   for my $pid (@display_pids) {
    my $u = `ps -o user= -p $pid 2>/dev/null`;
    chomp $u; $u =~ s/\s+//g; $u ||= "unknown";
    push @user_order, $u unless exists $by_user{$u};
    push @{$by_user{$u}}, $pid;
   }
   for my $u (@user_order) {
    say_out "\n[User: $u]\n";
    for my $pid (@{$by_user{$u}}) {
     my $cmd       = $pid_errors{$pid}->{cmd} // "";
     my $err_total = $pid_errors{$pid}->{total};
     say_out "\n  [PID $pid]" . ($cmd ? "  ($cmd)" : "") . "\n";
     say_out "    Total Errors : $err_total\n";
     say_out "    Confidence   : " . calc_confidence($err_total) . "%\n";
     process_stats_annotation($pid, "    ");
     show_process_tree($pid, "    ");
     show_syscall_hotspots($pid, $strace_timeout, "    ");
     for my $e (sort keys %{$pid_errors{$pid}->{errors}}) {
      my $edata = $pid_errors{$pid}->{errors}{$e};
      say_out sprintf("    %-15s %d  --  %s\n",
                      $e . ":",
                      $edata->{count},
                      ($error_causes{$e} // "Unknown"));
      show_error_extracted($edata, $e, "  ");
     }
     show_pid_context_terminal($pid, "    ") if $context_only;
    }
   }

  } elsif ($group_by_service) {
   # Group display PIDs by service name (command match)
   my %by_svc;
   my @svc_order;
   for my $pid (@display_pids) {
    my $cmd = $pid_errors{$pid}->{cmd} // "";
    my $svc = "other";
    for my $s (split /,/, $service) {
     if ($cmd && $cmd =~ /\Q$s\E/i) { $svc = $s; last }
    }
    push @svc_order, $svc unless exists $by_svc{$svc};
    push @{$by_svc{$svc}}, $pid;
   }
   for my $svc (@svc_order) {
    say_out "\n[Service: $svc]\n";
    for my $pid (@{$by_svc{$svc}}) {
     my $cmd       = $pid_errors{$pid}->{cmd} // "";
     my $err_total = $pid_errors{$pid}->{total};
     say_out "\n  [PID $pid]" . ($cmd ? "  ($cmd)" : "") . "\n";
     say_out "    Total Errors : $err_total\n";
     say_out "    Confidence   : " . calc_confidence($err_total) . "%\n";
     process_stats_annotation($pid, "    ");
     show_process_tree($pid, "    ");
     show_syscall_hotspots($pid, $strace_timeout, "    ");
     for my $e (sort keys %{$pid_errors{$pid}->{errors}}) {
      my $edata = $pid_errors{$pid}->{errors}{$e};
      say_out sprintf("    %-15s %d  --  %s\n",
                      $e . ":",
                      $edata->{count},
                      ($error_causes{$e} // "Unknown"));
      show_error_extracted($edata, $e, "  ");
     }
     show_pid_context_terminal($pid, "    ") if $context_only;
    }
   }

  } else {
   # Default: list each PID with UID shown inline
   for my $pid (@display_pids) {
    my $cmd       = $pid_errors{$pid}->{cmd} // "";
    my $uid       = `ps -o uid= -p $pid 2>/dev/null`;  chomp $uid; $uid =~ s/\s+//g;
    my $err_total = $pid_errors{$pid}->{total};
    my $uid_str   = defined $uid && $uid =~ /^\d+$/ ? "  uid=$uid" : "";
    say_out "\n[PID $pid]" . ($cmd ? "  ($cmd)" : "") . "$uid_str\n";
    say_out "  Total Errors : $err_total\n";
    say_out "  Confidence   : " . calc_confidence($err_total) . "%\n";
    process_stats_annotation($pid);
    show_process_tree($pid, "  ");
    show_syscall_hotspots($pid, $strace_timeout, "  ");
    for my $e (sort keys %{$pid_errors{$pid}->{errors}}) {
     my $edata = $pid_errors{$pid}->{errors}{$e};
     say_out sprintf("  %-15s %d  --  %s\n",
                     $e . ":",
                     $edata->{count},
                     ($error_causes{$e} // "Unknown"));
     show_error_extracted($edata, $e, "");
    }
    show_pid_context_terminal($pid, "  ") if $context_only;
   }
  }

  say_out "\n";
 }

 # --- SERVICE ERROR BREAKDOWN (Change 7) ---
 if ($service && $total_errors > 0) {
  say_out "SERVICE ERROR BREAKDOWN\n";
  say_out "=====================================\n";
  my %svc_pids;
  my %svc_errors;
  my @error_pids_all = sort grep { ($pid_errors{$_}->{total} // 0) > 0 } keys %pid_errors;
  for my $pid (@error_pids_all) {
   my $cmd = $pid_errors{$pid}->{cmd} // "";
   my $matched_svc = "other";
   for my $svc (split /,/, $service) {
    if ($cmd && $cmd =~ /\Q$svc\E/i) { $matched_svc = $svc; last; }
   }
   $svc_pids{$matched_svc}++;
   $svc_errors{$matched_svc} += $pid_errors{$pid}->{total} // 0;
  }
  for my $svc (sort keys %svc_pids) {
   say_out sprintf("  %-12s  --  %d PID(s), %d errors total\n",
                   $svc, $svc_pids{$svc}, $svc_errors{$svc});
  }
  say_out "\n";
 }

 # --- error timeline ---
 show_error_timeline() if $total_errors > 0;

 # --- RSS growth ---
 show_rss_growth();

 # --- cPanel log correlation ---
 correlate_logs($trace_start_time // time(), $trace_end_time // time())
  if ($total_errors > 0 && $total_traced > 0 &&
      (-d "/usr/local/cpanel" || -d "/opt/cpanel"));

 # --- global summary (always shown) ---
 say_out "\nGLOBAL SUMMARY\n";
 say_out "-------------------------------------\n";
 say_out "Processes Traced : $total_traced\n";
 say_out "Errors Found     : $total_errors";
 say_out $total_errors ? "" : "  (no errors detected)";
 say_out "\n";
 if ($total_errors) {
  say_out "Overall Confidence: " . calc_confidence($total_errors) . "%\n";
 }

 # Health alert echo in GLOBAL SUMMARY (Change 8)
 if (($status || $incident_mode) && %health_summary) {
  for my $label (sort keys %health_summary) {
   say_out "Health Alert     : $label ($health_summary{$label})\n";
  }
 }

 # PID existence check: warn for any requested PID that is no longer present.
 if ($pid_filter) {
  for my $rp (split /,/, $pid_filter) {
   $rp =~ s/\s+//g;
   next unless $rp =~ /^\d+$/;
   if (!-d "/proc/$rp") {
    say_out "\n[NOTE] PID $rp no longer exists -- process exited during or before the trace window.\n";
   }
  }
 }

 if ($d_state_skipped) {
  say_out "\n[NOTE] $d_state_skipped process(es) skipped -- uninterruptible sleep (D state)\n";
  say_out "       D-state processes are blocked in the kernel and cannot be traced.\n";
  say_out "       They are typically waiting on I/O, a hung network mount, or a locked\n";
  say_out "       kernel resource.  Investigate with: ps aux | grep ' D '\n";
 }
 if ($ptrace_denied) {
  say_out "\n[NOTE] $ptrace_denied process(es) could not be traced -- Operation not permitted\n";
  say_out "       Possible causes and resolutions:\n";
  for my $hint (ptrace_denial_hints()) {
   say_out "         $hint\n";
  }
 }
 say_out "\n";

 # --- shared failure correlation ---
 if ($total_errors > 0) {
  my $shared = find_shared_failures();
  my @shared_paths = sort {
   scalar(@{$shared->{paths}{$b}}) <=> scalar(@{$shared->{paths}{$a}})
  } keys %{$shared->{paths}};
  my @shared_addrs = sort {
   scalar(@{$shared->{addrs}{$b}}) <=> scalar(@{$shared->{addrs}{$a}})
  } keys %{$shared->{addrs}};

  if (@shared_paths || @shared_addrs) {
   say_out "SHARED FAILURES  (same target seen in 2+ processes)\n";
   say_out "-------------------------------------\n";
   for my $t (@shared_paths) {
    my $pids  = $shared->{paths}{$t};
    my $cmds  = join(", ", map { $pid_errors{$_}->{cmd} // $_ } @$pids);
    say_out sprintf("  %-50s  %d PIDs  (%s)\n", $t, scalar(@$pids), $cmds);
    my ($short, $detail) = path_hint($t);
    if ($short) {
     say_out "    [!] $short\n";
     say_out "        -> $detail\n";
    }
   }
   for my $t (@shared_addrs) {
    my $pids  = $shared->{addrs}{$t};
    my $cmds  = join(", ", map { $pid_errors{$_}->{cmd} // $_ } @$pids);
    say_out sprintf("  %-50s  %d PIDs  (%s)\n", $t, scalar(@$pids), $cmds);
    my ($port) = $t =~ /:(\d+)$/;
    my ($svc, $cmd) = port_hint($port);
    if ($svc) {
     say_out "    [!] $svc not responding\n";
     say_out "        -> $cmd\n";
    }
   }
   say_out "\n";
  }
 }

 # --- optional analysis passes ---
 show_segs_summary() if $segs;
 check_csf()         if $csf;
 find_similar()      if $similar;
 write_report()      if $report;

 # --- WATCH SUMMARY (Change 9) ---
 if (defined $watch && %watch_match_count) {
  say_out "\nWATCH SUMMARY\n";
  say_out "=====================================\n";
  say_out "Pattern: $watch\n";
  for my $pid (sort { $watch_match_count{$b} <=> $watch_match_count{$a} }
               keys %watch_match_count) {
   my $wcmd = $pid_errors{$pid}->{cmd} // "?";
   say_out sprintf("  PID %-7s  (%-15s)  %d matches\n",
                   $pid, $wcmd, $watch_match_count{$pid});
  }
  say_out "\n";
 }

 # --- json-only output ---
 if ($json_only) {
  my %out_processes;
  my %all = (%pid_errors, %syscall_count);
  for my $pid (sort keys %all) {
   my $cmd = `ps -o comm= -p $pid 2>/dev/null`;
   chomp $cmd;
   my $err_total = $pid_errors{$pid}->{total} // 0;
   my %errs;
   if (my $e = $pid_errors{$pid}->{errors}) {
    for my $ek (keys %$e) {
     $errs{$ek} = $e->{$ek}->{count};
    }
   }
   my @top_syscalls;
   if ($syscall_count{$pid}) {
    @top_syscalls = sort { $syscall_count{$pid}{$b} <=> $syscall_count{$pid}{$a} }
                        keys %{$syscall_count{$pid}};
    @top_syscalls = @top_syscalls[0..4] if @top_syscalls > 5;
   }
   $out_processes{$pid} = {
    command      => ($cmd || "unknown"),
    total_errors => $err_total,
    confidence   => calc_confidence($err_total),
    errors       => \%errs,
    top_syscalls => \@top_syscalls,
   };
  }

  my %json_out = (
   version   => $VERSION,
   timestamp => time(),
   profiles  => \@profiles,
   processes => \%out_processes,
   global    => {
    processes_traced   => $total_traced,
    total_errors       => $total_errors,
    overall_confidence => calc_confidence($total_errors),
   },
  );

  print to_json(\%json_out) . "\n";
 }

 write_log();

 say_out "Bye :)\n";
 exit 0;
}


# =============================================
# STATUS HEALTH CHECK
# Run before the main loop when --status is active (not --incident-mode,
# which already ran its own health check in the INCIDENT MODE block above).
# =============================================
if ($status && !$incident_mode) {
 say_out "\nSTATUS CHECK\n";
 say_out "=====================================\n";
 say_out "All profiles | Top $top_n PIDs\n";
 say_out "(Use --top=N to change the limit)\n\n";

 my $st_health   = check_system_health();
 my $st_critical = print_system_health($st_health);

 if ($st_critical) {
  say_out "[!] One or more metrics are CRITICAL.\n";
  say_out "    For a comprehensive 60-second incident capture, run:\n\n";
  say_out "      smartstrace --incident-mode\n\n";
  say_out "    Continuing with status analysis...\n\n";
 }
}


# =============================================
# MAIN EXECUTION
# =============================================
say_out "smartstrace v$VERSION running...\n";

$SIG{INT} = \&finish;

# Timeout: 5s normal, 2s quick, 60s incident (ignored when --run is set)
my $timeout = 5;
$timeout = 2  if $quick;
$timeout = 60 if $incident_mode;

my $end_time = time() + $timeout unless $run;

# Per-PID strace timeout (seconds)
$strace_timeout = 2;
$strace_timeout = 1 if $quick;
$strace_timeout = 5 if $incident_mode;

# Suppress startup line for --quick brief mode
say_out "Mode: " . do {
 my @modes;
 push @modes, "quick (${timeout}s)"      if $quick;
 push @modes, "incident (${timeout}s)"   if $incident_mode;
 push @modes, "continuous"               if $run;
 push @modes, "profiles: " . join(",", @profiles) if @profiles;
 push @modes, "json-only"                if $json_only;
 push @modes, "json-stream"              if $json_stream;
 @modes ? join(", ", @modes) : "standard (${timeout}s)";
} . "\n";


# =============================================
# MAIN LOOP
# =============================================
while (1) {

 $trace_start_time //= time();

 last if (!$run && time() >= $end_time);

 # Periodic RSS re-sampling every 15 seconds
 {
  my $now = time();
  if (!defined $last_rss_sample || $now - $last_rss_sample >= 15) {
   $last_rss_sample = $now;
   for my $rpid (keys %pid_errors) {
    next unless $rpid =~ /^\d+$/;
    my $rss_val = `ps -o rss= -p $rpid 2>/dev/null`;
    chomp $rss_val;
    $rss_val =~ s/^\s+//;
    if (defined $rss_val && $rss_val =~ /^\d+$/) {
     $pid_rss_initial{$rpid} //= $rss_val + 0;
     if (!defined $pid_rss_peak{$rpid} || $rss_val + 0 > $pid_rss_peak{$rpid}) {
      $pid_rss_peak{$rpid} = $rss_val + 0;
     }
    }
   }
  }
 }

 my @targets;

 # ---------------------------------------------------
 # TARGET SELECTION
 # Priority: --pid > --user > --service > profiles > default top-N
 # ---------------------------------------------------

 if ($pid_filter) {

  my @req_pids = split /,/, $pid_filter;
  for my $rp (@req_pids) {
   $rp =~ s/\s+//g;
   next unless $rp =~ /^\d+$/;
   if (-d "/proc/$rp") {
    push @targets, $rp;
   } else {
    print "\nInvalid PID: $rp\n\n";
    exit 1;
   }
  }

 }
 elsif ($user) {

  # --user supports comma-separated list
  my @users = split /,/, $user;
  for my $u (@users) {
   my @found = `pgrep -u $u 2>/dev/null`;
   chomp @found;
   push @targets, @found if @found;
  }

 }
 elsif ($service) {

  # Refresh service PIDs every iteration so restarted processes
  # are picked up automatically in --run mode (FIX #3)
  @target_pids = ();
  for my $svc (split /,/, $service) {
   my @found = `pgrep -x $svc 2>/dev/null`;
   chomp @found;
   if (!@found) {
    @found = `pgrep -f "\\b\\Q$svc\\E\\b" 2>/dev/null`;
    chomp @found;
   }
   push @target_pids, @found if @found;
  }
  @targets = @target_pids;

 }
 elsif (@profiles) {

  # Profile-specific process targeting (php -> pgrep, mysql -> pgrep,
  # network/io -> top-N by CPU, user -> pgrep by username)
  @targets = get_profile_targets(@profiles);

 }
 else {

  # Default: top-N processes by CPU (all selected regardless of usage level)
  my $limit = $top_n + 1;
  my @rows  = `ps -eo pid,ppid,%cpu,%mem,rss,etimes --sort=-%cpu 2>/dev/null | head -$limit`;
  shift @rows;
  chomp @rows;

  for my $row (@rows) {
   $row =~ s/^\s+//;
   my ($pid, $ppid, $cpu, $mem, $rss, $etimes) = split /\s+/, $row;
   next unless defined $pid && $pid =~ /^\d+$/;
   next if $pid == $$ || (defined $ppid && $ppid == $$);
   $pid_cpu{$pid}    = $cpu    + 0 if defined $cpu;
   $pid_mem{$pid}    = $mem    + 0 if defined $mem;
   $pid_rss{$pid}    = $rss    + 0 if defined $rss;
   $pid_etimes{$pid} = $etimes + 0 if defined $etimes;
   push @targets, $pid;
  }

 }

 # ---------------------------------------------------
 # SERVICE TRACE SUMMARY (Change 6)
 # Print once before tracing begins when --service is used.
 # ---------------------------------------------------
 if ($service && !$service_summary_shown) {
  say_out "\nSERVICE TRACE SUMMARY\n";
  say_out "=====================================\n";
  my $my_pid_ss  = $$;
  my $par_pid_ss = getppid();
  for my $svc (split /,/, $service) {
   my @spids = `pgrep -x $svc 2>/dev/null`; chomp @spids;
   @spids = grep { $_ != $my_pid_ss && $_ != $par_pid_ss } @spids;
   unless (@spids) {
    @spids = `pgrep -f "\\b$svc\\b" 2>/dev/null`; chomp @spids;
    @spids = grep { $_ != $my_pid_ss && $_ != $par_pid_ss } @spids;
   }
   if (@spids) {
    my @display_pids_ss = @spids > 5 ? (@spids[0..4]) : @spids;
    my $extra = @spids > 5 ? sprintf(" and %d more", scalar(@spids) - 5) : "";
    say_out sprintf("  %-12s  %s    (%d to trace)\n",
                    $svc,
                    c_green(sprintf("RUNNING    PIDs: %s%s",
                                    join(", ", @display_pids_ss), $extra)),
                    scalar @spids);
   } else {
    say_out sprintf("  %-12s  %s\n", $svc, c_red("NOT RUNNING  --  no processes found"));
   }
  }
  say_out "\n";
  $service_summary_shown = 1;
 }

 # ---------------------------------------------------
 # ALERT-CPU CHECK
 # Run after targets are finalized; warn if any target
 # exceeds the --alert-cpu threshold.
 # ---------------------------------------------------
 if (defined $alert_cpu) {
  for my $tpid (@targets) {
   next if $alerted_cpu{$tpid};
   my $cpu = `ps -o %cpu= -p $tpid 2>/dev/null`;
   chomp $cpu;
   $cpu =~ s/^\s+//;
   if (defined $cpu && $cpu =~ /^\d/ && $cpu >= $alert_cpu) {
    print "[ALERT] PID $tpid CPU at ${cpu}% (threshold: ${alert_cpu}%)\n";
    json_event({event => "alert_cpu", pid => $tpid, cpu => $cpu, threshold => $alert_cpu});
    $alerted_cpu{$tpid} = 1;
   }
  }
 }

 # ---------------------------------------------------
 # EXECUTION LOOP
 # ---------------------------------------------------
 for my $pid (@targets) {

  # Honour the timeout even when the target list is large
  # (e.g. --user=root with 100+ processes). Without this check
  # the outer while(1) guard is only hit after every PID has been
  # straced, which can take far longer than the intended window.
  last if (!$run && time() >= $end_time);

  chomp $pid;
  next unless $pid =~ /^\d+$/;
  next unless -d "/proc/$pid";

  # Capture process name now, while the process is alive.
  # Store it so it's available in analysis and log even if the process exits.
  unless (defined $pid_errors{$pid}->{cmd}) {
   if (open(my $commf, "<", "/proc/$pid/comm")) {
    my $cmd = <$commf>; close $commf;
    if (defined $cmd) { chomp $cmd; $pid_errors{$pid}->{cmd} = $cmd; }
   }
   # Capture CPU/mem/rss/etimes for --pid mode (selection loops handle the rest)
   unless (defined $pid_cpu{$pid}) {
    my $row = `ps -p $pid -o %cpu,%mem,rss,etimes --no-headers 2>/dev/null`;
    if (defined $row) {
     $row =~ s/^\s+//; chomp $row;
     my ($cpu, $mem, $rss, $etimes) = split /\s+/, $row;
     $pid_cpu{$pid}    = $cpu    + 0 if defined $cpu    && $cpu    =~ /^\d/;
     $pid_mem{$pid}    = $mem    + 0 if defined $mem    && $mem    =~ /^\d/;
     $pid_rss{$pid}    = $rss    + 0 if defined $rss    && $rss    =~ /^\d/;
     $pid_etimes{$pid} = $etimes + 0 if defined $etimes && $etimes =~ /^\d/;
    }
   }
  }

  # Skip processes in uninterruptible sleep (D state).
  # ptrace cannot attach to a D-state process -- the target cannot receive
  # SIGSTOP or deliver ptrace events while blocked in the kernel.  Worse,
  # if strace attaches just before the process enters D state, the strace
  # child itself can get stuck in D state trying to PTRACE_DETACH on exit,
  # making it immune even to SIGKILL.  Skipping D-state processes is safer
  # than attempting to trace them.
  {
   my $proc_state = "";
   if (open(my $sf, "<", "/proc/$pid/status")) {
    while (<$sf>) { if (/^State:\s+(\S)/) { $proc_state = $1; last; } }
    close $sf;
   }
   if ($proc_state eq 'D') {
    my $cmd = $pid_errors{$pid}->{cmd} // "";
    say_out "[SKIP] PID $pid" . ($cmd ? " ($cmd)" : "") .
            " -- uninterruptible sleep (D state), cannot be traced\n";
    $d_state_skipped++;
    next;
   }
  }

  $total_traced++;

  json_event({event => "trace_start", pid => $pid});

  # Fork-based open so we can redirect strace's stderr into the read pipe.
  # strace writes all syscall output to stderr by default. The previous
  # list-form open() captured only stdout, so every strace line was leaking
  # straight to the terminal.  With the fork approach we merge stderr into
  # stdout inside the child before exec(), keeping list-form argument safety
  # (no shell is involved -- args are passed directly to execvp).
  defined(my $child_pid = open(my $fh, "-|")) or do {
   $total_traced--;
   next;
  };

  if ($child_pid == 0) {
   # Child process: merge stderr -> stdout, then exec strace.
   open(STDERR, ">&STDOUT") or exit(1);
   # --kill-after=3 ensures strace receives SIGKILL 3 seconds after SIGTERM
   # if it hasn't exited yet.  This prevents strace from hanging indefinitely
   # in PTRACE_DETACH when the tracee transitions to D state after attachment.
   exec("timeout", "--kill-after=3", $strace_timeout, "strace", "-fp", $pid,
        @default_str_size, @profile_strace_args, @strace_extra);
   exit(1);
  }

  my $line_count = 0;

  while (<$fh>) {

   $line_count++;
   last if (!$run && time() >= $end_time);

   # Detect ptrace permission failure.
   # strace prints this to stderr when it cannot attach to a process.
   # We now capture stderr (merged into stdout above), so we can catch
   # it here and tell the user instead of silently counting the PID as
   # traced or letting the raw error text leak to the terminal.
   if (/ptrace[^:]*:\s*Operation not permitted/i
       || /attach:\s*ptrace/i
       || /PTRACE_SEIZE[^:]*:\s*Operation not permitted/i) {
    $ptrace_denied++;
    $total_traced--;   # don't count a failed attach as a traced process
    last;
   }

   # syscall tracking
   if (/\b([a-zA-Z0-9_]+)\(/) {
    $syscall_count{$pid}->{$1}++;
   }

   # Update rolling context buffer (last $context_n lines per PID, used for error context)
   {
    my $buf = ($pid_context{$pid} //= []);
    (my $t = $_) =~ s/^\s+|\s+$//g;
    push @$buf, $t;
    shift @$buf if @$buf > $context_n;
   }

   # error tracking
   if (/(ENOENT|EACCES|ETIMEDOUT|ECONNREFUSED|SIGSEGV|EMFILE|ENOSPC|EADDRINUSE)/) {
    my $err = $1;
    $pid_errors{$pid}->{total}++;
    $pid_errors{$pid}->{errors}{$err}->{count}++;
    $total_errors++;

    # Record timestamp for burst detection
    push @{$pid_errors{$pid}->{errors}{$err}->{timestamps}}, time();

    # Extract path argument for file-related errors (ENOENT, EACCES, ENOSPC).
    # Matches the first quoted path-like string in the syscall arguments.
    if ($err eq 'ENOENT' || $err eq 'EACCES' || $err eq 'ENOSPC') {
     if (/[,(]\s*"((?:\/|\.\.?\/)[^"]{1,511})"/) {
      $pid_errors{$pid}->{errors}{$err}->{paths}{$1}++;
     }
    }

    # Extract connect destination for network errors (ECONNREFUSED, ETIMEDOUT, EADDRINUSE).
    if ($err eq 'ECONNREFUSED' || $err eq 'ETIMEDOUT' || $err eq 'EADDRINUSE') {
     if (/sin_port=htons\((\d+)\).*?sin_addr=inet_addr\("([^"]+)"\)/) {
      $pid_errors{$pid}->{errors}{$err}->{addrs}{"$2:$1"}++;
     } elsif (/sin6_port=htons\((\d+)\).*?inet_pton\(AF_INET6,\s*"([^"]+)"\)/) {
      $pid_errors{$pid}->{errors}{$err}->{addrs}{"[$2]:$1"}++;
     } elsif (/sun_path="([^"]{1,256})"/) {
      $pid_errors{$pid}->{errors}{$err}->{addrs}{$1}++;
     }
    }

    # Capture context block for log detail (up to 10 unique blocks per error type per PID).
    # Each block = last 3 lines leading into the error + the error line itself.
    # Deduplication is on the error line so repeated identical failures don't flood the log.
    my $blocks = ($pid_errors{$pid}->{errors}{$err}->{blocks} //= []);
    if (@$blocks < 10) {
     (my $err_line = $_) =~ s/^\s+|\s+$//g;
     unless (grep { $_->[-1] eq $err_line } @$blocks) {
      my @ctx = @{$pid_context{$pid} // []};
      push @$blocks, [@ctx];  # ctx already includes the error line (last push above)
     }
    }

    json_event({event => "error", pid => $pid, error => $err,
                pid_total => $pid_errors{$pid}->{total}});

    # --segs: live alert on segfault
    if ($segs && $err eq 'SIGSEGV') {
     print "[SIGSEGV] PID $pid -- segmentation fault detected\n";
    }

    # --alert-errors: live alert when per-PID error count crosses threshold
    if (defined $alert_errors && !$alerted_errors{$pid}) {
     my $count = $pid_errors{$pid}->{total};
     if ($count >= $alert_errors) {
      print "[ALERT] PID $pid exceeded $alert_errors errors ($count total)\n";
      json_event({event => "alert_errors", pid => $pid,
                  count => $count, threshold => $alert_errors});
      $alerted_errors{$pid} = 1;
     }
    }
   }

   if (defined $watch_pattern && /$watch_pattern/) {
    $watch_match_count{$pid}++;
    my $now = time();
    if (!$watch_last_alert{$pid} || $now - $watch_last_alert{$pid} >= $watch_cooldown) {
     chomp(my $matched = $_);
     my $wcmd = $pid_errors{$pid}->{cmd} // "?";
     print "[WATCH] PID $pid ($wcmd)  $matched\n";
     $watch_last_alert{$pid} = $now;
    }
   }

   last if $line_count > 5000;
  }

  close $fh;
  json_event({event => "trace_end", pid => $pid,
              errors => ($pid_errors{$pid}->{total} // 0)});
 }

 sleep 1;
}


# =============================================
# FINAL EXECUTION HANDOFF
# FIX #8: call named finish() sub directly instead of $SIG{INT}->()
# =============================================
unless ($run) {
 finish();
}

