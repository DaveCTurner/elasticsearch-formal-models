#!/usr/bin/perl

use strict;

my @assms = ();

print <<EOF;
digraph G {
  rankdir="LR"
  node[color="red",penwidth=4]
EOF

while (<>) {
  chomp;
  if (/^lemma/) {
    @assms = ();
  } elsif (/^  assumes "([st]) *\\<Turnstile> *(\w+)/) {
    unshift @assms, {state => $1, assm => $2};
  } elsif (/^  shows.*\\<Turnstile> *(\w+)/) {
    my $conclusion = $1;
    print "$conclusion [shape=\"box\",color=\"black\"]\n";
    for my $assm (@assms) {
      my $assmname = $assm->{assm};
      next if $assmname eq $conclusion;
      my $style = $assm->{state} eq 's' ? '[arrowhead="normal",penwidth=2]' : '[arrowhead="onormal",color="red",penwidth=2]';
      print "  $assmname -> $conclusion $style\n";
    }
    @assms = ();
  }
}

print <<EOF;
}
EOF
