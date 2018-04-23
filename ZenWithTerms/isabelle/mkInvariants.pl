#!/usr/bin/perl

use strict;

my @assms = ();
my $conclusion;
my $unproved = 0;

print <<EOF;
digraph G {
  rankdir="LR"
  node[color="red",shape="box",penwidth=4]
EOF

while (<>) {
  chomp;
  if (/^lemma/) {

    if ($conclusion) {
      my $conclusionColour = $unproved ? 'goldenrod' : 'forestgreen';
      print "  $conclusion [color=\"$conclusionColour\"]\n";
      for my $assm (@assms) {
        my $assmname = $assm->{assm};
        next if $assmname eq $conclusion;
        my $style = $assm->{state} eq 's' ? '[arrowhead="normal",color="forestgreen",penwidth=2]' : '[arrowhead="onormal",color="goldenrod",penwidth=2]';
        print "  $assmname -> $conclusion $style\n";
      }
    }

    @assms = ();
    undef $conclusion;
    $unproved = 0;

  } elsif (/^  assumes "([st]) *\\<Turnstile> *(\w+)/) {
    unshift @assms, {state => $1, assm => $2};
  } elsif (/^  shows.*\\<Turnstile> *(\w+)/) {
    $conclusion = "$1";
  } elsif (/sorry/) {
    $unproved = 1;
  }
}

print <<EOF;
}
EOF
