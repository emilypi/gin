#!/bin/sh
set -eu
cd "$(dirname "$0")/.."

# Generated golden files and canonical data retain their bytes. Everything
# else below is authored source, configuration, or a Markdown code fence.
git ls-files --cached --others --exclude-standard -z \
  '*.hs' '*.lean' '*.sh' '*.sv' '*.v' '*.vhd' '*.cabal' \
  '*.yaml' '*.yml' 'cabal.project' '*.md' |
  xargs -0 perl -e '
    use open qw(:std :encoding(UTF-8));
    my ($previous, $line, $fenced, $failed) = ("", 0, 0, 0);
    while (<>) {
      if ($ARGV ne $previous) {
        ($previous, $line, $fenced) = ($ARGV, 0, 0);
      }
      ++$line;
      next if $ARGV =~ m{^test/golden/};
      if ($ARGV =~ /\.md$/) {
        if (/^\s*```/) { $fenced = !$fenced; next; }
        next unless $fenced;
      }
      chomp;
      my $columns = 0;
      for my $character (split //) {
        $columns += $character eq "\t" ? 8 - $columns % 8 : 1;
      }
      if ($columns > 90) {
        printf "%s:%d: %d columns\n", $ARGV, $line, $columns;
        $failed = 1;
      }
    }
    exit $failed;
  '
