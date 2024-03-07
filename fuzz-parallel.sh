#!/usr/bin/bash

# Copyright (C) 2007-2023 noteness, Ole Tange, http://ole.tange.dk
# and Free Software Foundation, Inc.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, see <https://www.gnu.org/licenses/>
# or write to the Free Software Foundation, Inc., 51 Franklin St,
# Fifth Floor, Boston, MA 02110-1301 USA

# Embedded GNU Parallel created with --embed
parallel() {
    # Start GNU	 Parallel without leaving temporary files
    #
    # Not all shells support 'perl <(cat ...)'
    # This is a complex way of doing:
    #	perl <(cat <<'cut-here'
    #	  [...]
    #	  ) "$@"
    # and also avoiding:
    #	[1]+  Done   cat

    # Make a temporary fifo that perl can read from
    _fifo_with_GNU_Parallel_source=`perl -e 'use POSIX qw(mkfifo);
      do {
	$f = "/tmp/parallel-".join"",
	  map { (0..9,"a".."z","A".."Z")[rand(62)] } (1..5);
      } while(-e $f);
      mkfifo($f,0600);
      print $f;'`
    # Put source code into temporary file
    # so it is easy to copy to the fifo
    _file_with_GNU_Parallel_source=`mktemp`;
cat <<'cut-here-V93TWypzvAaP5RvzZfUv' > $_file_with_GNU_Parallel_source
#!/usr/bin/perl

# Copyright (C) 2007-2023 Ole Tange, http://ole.tange.dk and Free
# Software Foundation, Inc.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, see <https://www.gnu.org/licenses/>
# or write to the Free Software Foundation, Inc., 51 Franklin St,
# Fifth Floor, Boston, MA 02110-1301 USA
#
# SPDX-FileCopyrightText: 2007-2023 Ole Tange, http://ole.tange.dk and Free Software and Foundation, Inc.
# SPDX-License-Identifier: GPL-3.0-or-later

# open3 used in Job::start
use IPC::Open3;
use POSIX;
# gensym used in Job::start
use Symbol qw(gensym);
# tempfile used in Job::start
use File::Temp qw(tempfile tempdir);
# mkpath used in openresultsfile
use File::Path;
# GetOptions used in get_options_from_array
use Getopt::Long;
# Used to ensure code quality
use strict;
use File::Basename;

sub set_input_source_header($$) {
    my ($command_ref,$input_source_fh_ref) = @_;
    if(defined $opt::header and not $opt::pipe) {
	# split with colsep or \t
	# $header force $colsep = \t if undef?
	my $delimiter = defined $opt::colsep ? $opt::colsep : "\t";
	# regexp for {=
	my $left = "\Q$Global::parensleft\E";
	my $l = $Global::parensleft;
	# regexp for =}
	my $right = "\Q$Global::parensright\E";
	my $r = $Global::parensright;
	if($opt::header ne "0") {
	    my $id = 1;
	    for my $fh (@$input_source_fh_ref) {
		my $line = <$fh>;
		chomp($line);
		$line =~ s/\r$//;
		::debug("init", "Delimiter: '$delimiter'");
		for my $s (split /$delimiter/o, $line) {
		    ::debug("init", "Colname: '$s'");
		    # Replace {colname} with {2}
		    for(@$command_ref, @Global::ret_files,
			@Global::transfer_files, $opt::tagstring,
			$opt::workdir, $opt::results, $opt::retries,
			@Global::template_contents, @Global::template_names,
			@opt::filter) {
			# Skip if undefined
			$_ or next;
		      s:\{$s(|/|//|\.|/\.)\}:\{$id$1\}:g;
			# {=header1 ... =}  =>  {=1 ... =}
		      s:$left $s (.*?) $right:$l$id$1$r:gx;
		    }
		    $Global::input_source_header{$id} = $s;
		    $id++;
		}
	    }
	}
	# Make it possible to do:
	# parallel --header 0 echo {file2} {file1} :::: file1 file2
	my $id = 1;
	for my $s (@opt::a) {
	    # ::: are put into files and given a filehandle
	    # ignore these and only keep the filenames.
	    fileno $s and next;
	    for(@$command_ref, @Global::ret_files,
		@Global::transfer_files, $opt::tagstring,
		$opt::workdir, $opt::results, $opt::retries,
		@Global::template_contents, @Global::template_names,
		@opt::filter) {
		# Skip if undefined
		$_ or next;
	      s:\{\Q$s\E(|/|//|\.|/\.)\}:\{$id$1\}:g;
		# {=header1 ... =}  =>  {=1 ... =}
	      s:$left \Q$s\E (.*?) $right:$l$id$1$r:gx;
	    }
	    $Global::input_source_header{$id} = $s;
	    $id++;
	}
    } else {
	my $id = 1;
	for my $fh (@$input_source_fh_ref) {
	    $Global::input_source_header{$id} = $id;
	    $id++;
	}
    }
}

sub max_jobs_running() {
    # Compute $Global::max_jobs_running as the max number of jobs
    # running on each sshlogin.
    # Returns:
    #   $Global::max_jobs_running
    if(not $Global::max_jobs_running) {
	for my $sshlogin (values %Global::host) {
	    $sshlogin->max_jobs_running();
	}
    }
    if(not $Global::max_jobs_running) {
	::error("Cannot run any jobs.");
	wait_and_exit(255);
    }
    return $Global::max_jobs_running;
}

sub halt() {
    # Compute exit value,
    # wait for children to complete
    # and exit
    if($opt::halt and $Global::halt_when ne "never") {
	if(not defined $Global::halt_exitstatus) {
	    if($Global::halt_pct) {
		$Global::halt_exitstatus =
		    ::ceil($Global::total_failed /
			   ($Global::total_started || 1) * 100);
	    } elsif($Global::halt_count) {
		$Global::halt_exitstatus =
		    ::min(undef_as_zero($Global::total_failed),101);
	    }
	}
	wait_and_exit($Global::halt_exitstatus);
    } else {
	if($Global::semaphore) {
	    # --semaphore runs a single job:
	    # Use exit value of that
	    wait_and_exit($Global::halt_exitstatus);
	} else {
	    # 0 = all jobs succeeded
	    # 1-100 = n jobs failed
	    # 101 = >100 jobs failed
	    wait_and_exit(min(undef_as_zero($Global::exitstatus),101));
	}
    }
}


sub __PIPE_MODE__() {}


sub pipepart_setup() {
    # Compute the blocksize
    # Generate the commands to extract the blocks
    # Push the commands on queue
    # Changes:
    #   @Global::cat_prepends
    #   $Global::JobQueue
    if($opt::tee) {
	# Prepend each command with
	#   < file
	my $cat_string = "< ".Q($opt::a[0]);
	for(1..$Global::JobQueue->total_jobs()) {
	    push @Global::cat_appends, $cat_string;
	    push @Global::cat_prepends, "";
	}
    } else {
	if(not $opt::blocksize) {
	    # --blocksize with 10 jobs per jobslot
	    $opt::blocksize = -10;
	}
	if($opt::roundrobin) {
	    # --blocksize with 1 job per jobslot
	    $opt::blocksize = -1;
	}
	if($opt::blocksize < 0) {
	    my $size = 0;
	    # Compute size of -a
	    for(@opt::a) {
		if(-f $_) {
		    $size += -s $_;
		} elsif(-b $_) {
		    $size += size_of_block_dev($_);
		} elsif(-e $_) {
		    ::error("$_ is neither a file nor a block device");
		    wait_and_exit(255);
		} else {
		    ::error("File not found: $_");
		    wait_and_exit(255);
		}
	    }
	    # Run in total $job_slots*(- $blocksize) jobs
	    # Set --blocksize = size / no of proc / (- $blocksize)
	    $Global::dummy_jobs = 1;
	    $Global::blocksize = 1 +
		int($size / max_jobs_running() /
		    -multiply_binary_prefix($opt::blocksize));
	}
	@Global::cat_prepends = (map { pipe_part_files($_) }
				 # ::: are put into files and given a filehandle
				 # ignore these and only keep the filenames.
				 grep { ! fileno $_ } @opt::a);
	# Unget the empty arg as many times as there are parts
	$Global::JobQueue->{'commandlinequeue'}{'arg_queue'}->unget(
	    map { [Arg->new("\0noarg")] } @Global::cat_prepends
	    );
    }
}

sub pipe_tee_setup() {
    # Create temporary fifos
    # Run 'tee fifo1 fifo2 fifo3 ... fifoN' in the background
    # This will spread the input to fifos
    # Generate commands that reads from fifo1..N:
    #	cat fifo | user_command
    # Changes:
    #	@Global::cat_prepends
    my @fifos;
    for(1..$Global::JobQueue->total_jobs()) {
	push @fifos, tmpfifo();
    }
    # cat foo | tee fifo1 fifo2 fifo3 fifo4 fifo5 > /dev/null
    if(not fork()){
	# Test if tee supports --output-error=warn-nopipe
	`echo | tee --output-error=warn-nopipe /dev/null >/dev/null 2>/dev/null`;
	my $opt = $? ? "" : "--output-error=warn-nopipe";
	::debug("init","tee $opt");
	if($opt::dryrun) {
	    # This is not exactly what is run, but it gives the basic idea
	    print "mkfifo @fifos\n";
	    print "tee $opt @fifos >/dev/null &\n";
	} else {
	    # Let tee inherit our stdin
	    # and redirect stdout to null
	    open STDOUT, ">","/dev/null";
	    if($opt) {
		exec "tee", $opt, @fifos;
	    } else {
		exec "tee", @fifos;
	    }
	}
	exit(0);
    }
    # For each fifo
    #	(rm fifo1; grep 1) < fifo1
    #	(rm fifo2; grep 2) < fifo2
    #	(rm fifo3; grep 3) < fifo3
    # Remove the tmpfifo as soon as it is open
    @Global::cat_prepends = map { "(rm $_;" } shell_quote(@fifos);
    @Global::cat_appends = map { ") < $_" } shell_quote(@fifos);
}


sub parcat_script() {
    # TODO if script fails: Use parallel -j0 --plain --lb cat ::: fifos
    my $script = q'{
	use POSIX qw(:errno_h);
	use IO::Select;
	use strict;
	use threads;
	use Thread::Queue;
	use Fcntl qw(:DEFAULT :flock);

	my $opened :shared;
	my $q = Thread::Queue->new();
	my $okq = Thread::Queue->new();
	my @producers;

	if(not @ARGV) {
	    if(-t *STDIN) {
		print "Usage:\n";
		print "  parcat file(s)\n";
		print "  cat argfile | parcat\n";
	    } else {
		# Read arguments from stdin
		chomp(@ARGV = <STDIN>);
	    }
	}
	my $files_to_open = 0;
	# Default: fd = stdout
	my $fd = 1;
	for (@ARGV) {
	    # --rm = remove file when opened
	    /^--rm$/ and do { $opt::rm = 1; next; };
	    # -1 = output to fd 1, -2 = output to fd 2
	    /^-(\d+)$/ and do { $fd = $1; next; };
	    push @producers, threads->create("producer", $_, $fd);
	    $files_to_open++;
	}

	sub producer {
	    # Open a file/fifo, set non blocking, enqueue fileno of the file handle
	    my $file = shift;
	    my $output_fd = shift;
	    open(my $fh, "<", $file) || do {
		print STDERR "parcat: Cannot open $file\n";
		exit(1);
	    };
	    # Remove file when it has been opened
	    if($opt::rm) {
		unlink $file;
	    }
	    set_fh_non_blocking($fh);
	    $opened++;
	    # Pass the fileno to parent
	    $q->enqueue(fileno($fh),$output_fd);
	    # Get an OK that the $fh is opened and we can release the $fh
	    while(1) {
		my $ok = $okq->dequeue();
		if($ok == fileno($fh)) { last; }
		# Not ours - very unlikely to happen
		$okq->enqueue($ok);
	    }
	    return;
	}

	my $s = IO::Select->new();
	my %buffer;

	sub add_file {
	    my $infd = shift;
	    my $outfd = shift;
	    open(my $infh, "<&=", $infd) || die;
	    open(my $outfh, ">&=", $outfd) || die;
	    $s->add($infh);
	    # Tell the producer now opened here and can be released
	    $okq->enqueue($infd);
	    # Initialize the buffer
	    @{$buffer{$infh}{$outfd}} = ();
	    $Global::fh{$outfd} = $outfh;
	}

	sub add_files {
	    # Non-blocking dequeue
	    my ($infd,$outfd);
	    do {
		($infd,$outfd) = $q->dequeue_nb(2);
		if(defined($outfd)) {
		    add_file($infd,$outfd);
		}
	    } while(defined($outfd));
	}

	sub add_files_block {
	    # Blocking dequeue
	    my ($infd,$outfd) = $q->dequeue(2);
	    add_file($infd,$outfd);
	}


	my $fd;
	my (@ready,$infh,$rv,$buf);
	do {
	    # Wait until at least one file is opened
	    add_files_block();
	    while($q->pending or keys %buffer) {
		add_files();
		while(keys %buffer) {
		    @ready = $s->can_read(0.01);
		    if(not @ready) {
			add_files();
		    }
		    for $infh (@ready) {
			# There is only one key, namely the output file descriptor
			for my $outfd (keys %{$buffer{$infh}}) {
			    # TODO test if 60800 is optimal (2^17 is used elsewhere)
			    $rv = sysread($infh, $buf, 60800);
			    if (!$rv) {
				if($! == EAGAIN) {
				    # Would block: Nothing read
				    next;
				} else {
				    # Nothing read, but would not block:
				    # This file is done
				    $s->remove($infh);
				    for(@{$buffer{$infh}{$outfd}}) {
					syswrite($Global::fh{$outfd},$_);
				    }
				    delete $buffer{$infh};
				    # Closing the $infh causes it to block
				    # close $infh;
				    add_files();
				    next;
				}
			    }
			    # Something read.
			    # Find \n or \r for full line
			    my $i = (rindex($buf,"\n")+1);
			    if($i) {
				# Print full line
				for(@{$buffer{$infh}{$outfd}}, substr($buf,0,$i)) {
				    syswrite($Global::fh{$outfd},$_);
				}
				# @buffer = remaining half line
				$buffer{$infh}{$outfd} = [substr($buf,$i,$rv-$i)];
			    } else {
				# Something read, but not a full line
				push @{$buffer{$infh}{$outfd}}, $buf;
			    }
			    redo;
			}
		    }
		}
	    }
	} while($opened < $files_to_open);

	for (@producers) {
	    $_->join();
	}

	sub set_fh_non_blocking {
	    # Set filehandle as non-blocking
	    # Inputs:
	    #	$fh = filehandle to be blocking
	    # Returns:
	    #	N/A
	    my $fh = shift;
	    my $flags;
	    fcntl($fh, &F_GETFL, $flags) || die $!; # Get the current flags on the filehandle
	    $flags |= &O_NONBLOCK; # Add non-blocking to the flags
	    fcntl($fh, &F_SETFL, $flags) || die $!; # Set the flags on the filehandle
	}
    }';
    return ::spacefree(3, $script);
}

sub sharder_script() {
    my $script = q{
	use B;
	# Column separator
	my $sep = shift;
	# Which columns to shard on (count from 1)
	my $col = shift;
	# Which columns to shard on (count from 0)
	my $col0 = $col - 1;
	# Perl expression
	my $perlexpr = shift;
	my $bins = @ARGV;
	# Open fifos for writing, fh{0..$bins}
	my $t = 0;
	my %fh;
	for(@ARGV) {
	    open $fh{$t++}, ">", $_;
	    # open blocks until it is opened by reader
	    # so unlink only happens when it is ready
	    unlink $_;
	}
	if($perlexpr) {
	    my $subref = eval("sub { no strict; no warnings; $perlexpr }");
	    while(<STDIN>) {
		# Split into $col columns (no need to split into more)
		@F = split $sep, $_, $col+1;
		{
		    local $_ = $F[$col0];
		    &$subref();
		    $fh = $fh{ hex(B::hash($_))%$bins };
		}
		print $fh $_;
	    }
	} else {
	    while(<STDIN>) {
		# Split into $col columns (no need to split into more)
		@F = split $sep, $_, $col+1;
		$fh = $fh{ hex(B::hash($F[$col0]))%$bins };
		print $fh $_;
	    }
	}
	# Close all open fifos
	close values %fh;
    };
    return ::spacefree(1, $script);
}

sub binner_script() {
    my $script = q{
	use B;
	# Column separator
	my $sep = shift;
	# Which columns to shard on (count from 1)
	my $col = shift;
	# Which columns to shard on (count from 0)
	my $col0 = $col - 1;
	# Perl expression
	my $perlexpr = shift;
	my $bins = @ARGV;
	# Open fifos for writing, fh{0..$bins}
	my $t = 0;
	my %fh;
	# Let the last output fifo be the 0'th
	open $fh{$t++}, ">", pop @ARGV;
	for(@ARGV) {
	    open $fh{$t++}, ">", $_;
	    # open blocks until it is opened by reader
	    # so unlink only happens when it is ready
	    unlink $_;
	}
	if($perlexpr) {
	    my $subref = eval("sub { no strict; no warnings; $perlexpr }");
	    while(<STDIN>) {
		# Split into $col columns (no need to split into more)
		@F = split $sep, $_, $col+1;
		{
		    local $_ = $F[$col0];
		    &$subref();
		    $fh = $fh{ $_%$bins };
		}
		print $fh $_;
	    }
	} else {
	    while(<STDIN>) {
		# Split into $col columns (no need to split into more)
		@F = split $sep, $_, $col+1;
		$fh = $fh{ $F[$col0]%$bins };
		print $fh $_;
	    }
	}
	# Close all open fifos
	close values %fh;
    };
    return ::spacefree(1, $script);
}

sub pipe_shard_setup() {
    # Create temporary fifos
    # Run 'shard.pl sep col fifo1 fifo2 fifo3 ... fifoN' in the background
    # This will spread the input to fifos
    # Generate commands that reads from fifo1..N:
    #	cat fifo | user_command
    # Changes:
    #	@Global::cat_prepends
    my @shardfifos;
    my @parcatfifos;
    # TODO $opt::jobs should be evaluated (100%)
    # TODO $opt::jobs should be number of total_jobs if there are arguments
    max_jobs_running();
    my $njobs = $Global::max_jobs_running;
    for my $m (0..$njobs-1) {
	for my $n (0..$njobs-1) {
	    # sharding to A B C D
	    # parcatting all As together
	    $parcatfifos[$n][$m] = $shardfifos[$m][$n] = tmpfifo();
	}
    }
    my $shardbin = ($opt::shard || $opt::bin);
    my $script;
    if($opt::bin) {
	$script = binner_script();
    } else {
	$script = sharder_script();
    }

    # cat foo | sharder sep col fifo1 fifo2 fifo3 ... fifoN

    if($shardbin =~ /^[a-z_][a-z_0-9]*(\s|$)/i) {
	# Group by column name
	# (Yes, this will also wrongly match a perlexpr like: chop)
	my($read,$char,@line);
	# A full line, but nothing more (the rest must be read by the child)
	# $Global::header used to prepend block to each job
	do {
	    $read = sysread(STDIN,$char,1);
	    push @line, $char;
	} while($read and $char ne "\n");
	$Global::header = join "", @line;
    }
    my ($col, $perlexpr, $subref) =
	column_perlexpr($shardbin, $Global::header, $opt::colsep);
    if(not fork()) {
	# Let the sharder inherit our stdin
	# and redirect stdout to null
	open STDOUT, ">","/dev/null";
	# The PERL_HASH_SEED must be the same for all sharders
	# so B::hash will return the same value for any given input
	$ENV{'PERL_HASH_SEED'} = $$;
	exec qw(parallel -0 --block 100k -q --pipe -j), $njobs,
	    qw(--roundrobin -u perl -e), $script, ($opt::colsep || ","),
	    $col, $perlexpr, '{}', (map { (':::+', @{$_}) } @parcatfifos);
    }
    # For each fifo
    #	(rm fifo1; grep 1) < fifo1
    #	(rm fifo2; grep 2) < fifo2
    #	(rm fifo3; grep 3) < fifo3
    my $parcat = Q(parcat_script());
    if(not $parcat) {
	::error("'parcat' must be in path.");
	::wait_and_exit(255);
    }
    @Global::cat_prepends =
	map { "perl -e $parcat ".
		  join(" ",shell_quote(@$_))." | "} @parcatfifos;
}

sub pipe_part_files(@) {
    # Given the bigfile
    # find header and split positions
    # make commands that 'cat's the partial file
    # Input:
    #	$file = the file to read
    # Returns:
    #	@commands that will cat_partial each part
    my ($file) = @_;
    my $buf = "";
    if(not -f $file and not -b $file) {
	::error("--pipepart only works on seekable files, not streams/pipes.",
		"$file is not a seekable file.");
	::wait_and_exit(255);
    }

    my $fh = open_or_exit($file);
    my $firstlinelen = 0;
    if($opt::skip_first_line) {
	my $newline;
	# Read a full line one byte at a time
	while($firstlinelen += sysread($fh,$newline,1,0)) {
	    $newline eq "\n" and last;
	}
    }
    my $header = find_header(\$buf,$fh);
    # find positions
    my @pos = find_split_positions($file,int($Global::blocksize),
				   $header,$firstlinelen);
    # Make @cat_prepends
    my @cat_prepends = ();
    for(my $i=0; $i<$#pos; $i++) {
	push(@cat_prepends,
	     cat_partial($file, $firstlinelen, $firstlinelen+length($header),
			 $pos[$i], $pos[$i+1]));
    }
    return @cat_prepends;
}

sub find_header($$) {
    # Compute the header based on $opt::header
    # Input:
    #	$buf_ref = reference to read-in buffer
    #	$fh = filehandle to read from
    # Uses:
    #	$opt::header
    #	$Global::blocksize
    #	$Global::header
    # Returns:
    #	$header string
    my ($buf_ref, $fh) = @_;
    my $header = "";
    # $Global::header may be set in group_by_loop()
    if($Global::header) { return $Global::header }
    if($opt::header) {
	if($opt::header eq ":") { $opt::header = "(.*\n)"; }
	# Number = number of lines
	$opt::header =~ s/^(\d+)$/"(.*\n)"x$1/e;
	while(sysread($fh,$$buf_ref,int($Global::blocksize),length $$buf_ref)) {
	    if($$buf_ref =~ s/^($opt::header)//) {
		$header = $1;
		last;
	    }
	}
    }
    return $header;
}

sub find_split_positions($$$) {
    # Find positions in bigfile where recend is followed by recstart
    # Input:
    #	$file = the file to read
    #	$block = (minimal) --block-size of each chunk
    #	$header = header to be skipped
    # Uses:
    #	$opt::recstart
    #	$opt::recend
    # Returns:
    #	@positions of block start/end
    my($file, $block, $header, $firstlinelen) = @_;
    my $skiplen = $firstlinelen + length $header;
    my $size = -s $file;
    if(-b $file) {
	# $file is a blockdevice
	$size = size_of_block_dev($file);
    }
    $block = int $block;
    if($opt::groupby) {
	return split_positions_for_group_by($file,$size,$block,
					    $header,$firstlinelen);
    }
    # The optimal dd blocksize for mint, redhat, solaris, openbsd = 2^17..2^20
    # The optimal dd blocksize for freebsd = 2^15..2^17
    # The optimal dd blocksize for ubuntu (AMD6376) = 2^16
    my $dd_block_size = 131072; # 2^17
    my @pos;
    my ($recstart,$recend) = recstartrecend();
    my $recendrecstart = $recend.$recstart;
    my $fh = ::open_or_exit($file);
    push(@pos,$skiplen);
    for(my $pos = $block+$skiplen; $pos < $size; $pos += $block) {
	my $buf;
	if($recendrecstart eq "") {
	    # records ends anywhere
	    push(@pos,$pos);
	} else {
	    # Seek the the block start
	    if(not sysseek($fh, $pos, 0)) {
		::error("Cannot seek to $pos in $file");
		edit(255);
	    }
	    while(sysread($fh,$buf,$dd_block_size,length $buf)) {
		if($opt::regexp) {
		    # If match /$recend$recstart/ => Record position
		    if($buf =~ m:^(.*$recend)$recstart:os) {
			# Start looking for next record _after_ this match
			$pos += length($1);
			push(@pos,$pos);
			last;
		    }
		} else {
		    # If match $recend$recstart => Record position
		    # TODO optimize to only look at the appended
		    #	$dd_block_size + len $recendrecstart
		    # TODO increase $dd_block_size to optimize for longer records
		    my $i = index64(\$buf,$recendrecstart);
		    if($i != -1) {
			# Start looking for next record _after_ this match
			$pos += $i + length($recend);
			push(@pos,$pos);
			last;
		    }
		}
	    }
	}
    }
    if($pos[$#pos] != $size) {
	# Last splitpoint was not at end of the file: add $size as the last
	push @pos, $size;
    }
    close $fh;
    return @pos;
}

sub split_positions_for_group_by($$$$) {
    my($fh);
    my %value;
    sub value_at($) {
	my $pos = shift;
	if(not defined $value{$pos}) {
	    if($pos != 0) {
		seek($fh, $pos-1, 0) || die;
		# Read half line
		<$fh>;
	    }
	    # Read full line
	    my $linepos = tell($fh);
	    if(not defined $value{$linepos}) {
		$_ = <$fh>;
		if(defined $_) {
		    # Not end of file
		    my @F;
		    if(defined $group_by::col) {
			$opt::colsep ||= "\t";
			@F = split /$opt::colsep/, $_;
			$_ = $F[$group_by::col];
		    }
		    eval $group_by::perlexpr;
		}
		$value{$linepos} = [$_,$linepos];
	    }
	    $value{$pos} = $value{$linepos};
	}
	return (@{$value{$pos}});
    }

    sub binary_search_end($$$) {
	my ($s,$spos,$epos) = @_;
	# value_at($spos) == $s
	# value_at($epos) != $s
	my $posdif = $epos - $spos;
	my ($v,$vpos);
	while($posdif) {
	    ($v,$vpos) = value_at($spos+$posdif);
	    if($v eq $s) {
		$spos = $vpos;
		$posdif = $epos - $spos;
	    } else {
		$epos = $vpos;
	    }
	    $posdif = int($posdif/2);
	}
	return($v,$vpos);
    }

    sub binary_search_start($$$) {
	my ($s,$spos,$epos) = @_;
	# value_at($spos) != $s
	# value_at($epos) == $s
	my $posdif = $epos - $spos;
	my ($v,$vpos);
	while($posdif) {
	    ($v,$vpos) = value_at($spos+$posdif);
	    if($v eq $s) {
		$epos = $vpos;
	    } else {
		$spos = $vpos;
		$posdif = $epos - $spos;
	    }
	    $posdif = int($posdif/2);
	}
	return($v,$vpos);
    }

    my ($file,$size,$block,$header,$firstlinelen) = @_;
    my @pos;
    $fh = open_or_exit($file);
    # Set $Global::group_by_column $Global::group_by_perlexpr
    group_by_loop($fh,$opt::recsep);
    if($opt::max_args) {
	# Split after n values
	my ($a,$apos);
	# $xpos = linestart, $x = value at $xpos
	$apos = $firstlinelen + length $header;
	for(($a,$apos) = value_at($apos); $apos < $size;) {
	    push @pos, $apos;
	    ($a,$apos) = binary_search_end($a,$apos,$size);
	    if(eof($fh)) {
		push @pos, $size; last;
	    }
	}
	# @pos = start of every value
	# Merge n values
	# -nX = keep every X'th position
	my $i = 0;
	@pos = grep { not ($i++ % $opt::max_args) } @pos;
    } else {
	# Split after any value group
	# Preferable < $blocksize
	my ($a,$b,$c,$apos,$bpos,$cpos);
	# $xpos = linestart, $x = value at $xpos, $apos < $bpos < $cpos
	$apos = $firstlinelen + length $header;
	for(($a,$apos) = value_at($apos); $apos < $size;) {
	    push @pos, $apos;
	    $bpos = $apos + $block;
	    ($b,$bpos) = value_at($bpos);
	    if(eof($fh)) {
		# EOF is less than 1 block away
		push @pos, $size; last;
	    }
	    $cpos = $bpos + $block;
	    ($c,$cpos) = value_at($cpos);
	    if($a eq $b) {
		while($b eq $c) {
		    # Move bpos, cpos a block forward until $a == $b != $c
		    $bpos = $cpos;
		    $cpos += $block;
		    ($c,$cpos) = value_at($cpos);
		    if($cpos >= $size) {
			$cpos = $size;
			last;
		    }
		}
		# $a == $b != $c
		# Binary search for $b ending between ($bpos,$cpos)
		($b,$bpos) = binary_search_end($b,$bpos,$cpos);
	    } else {
		if($b eq $c) {
		    # $a != $b == $c
		    # Binary search for $b starting between ($apos,$bpos)
		    ($b,$bpos) = binary_search_start($b,$apos,$bpos);
		} else {
		    # $a != $b != $c
		    # Binary search for $b ending between ($bpos,$cpos)
		    ($b,$bpos) = binary_search_end($b,$bpos,$cpos);
		}
	    }
	    ($a,$apos) = ($b,$bpos);
	}
    }
    if($pos[$#pos] != $size) {
	# Last splitpoint was not at end of the file: add it
	push @pos, $size;
    }
    return @pos;
}

sub cat_partial($@) {
    # Efficient command to copy from byte X to byte Y
    # Input:
    #	$file = the file to read
    #	($start, $end, [$start2, $end2, ...]) = start byte, end byte
    # Returns:
    #	Efficient command to copy $start..$end, $start2..$end2, ... to stdout
    my($file, @start_end) = @_;
    my($start, $i);
    # Convert (start,end) to (start,len)
    my @start_len = map {
	if(++$i % 2) { $start = $_; } else { $_-$start }
    } @start_end;
    # The optimal block size differs
    # It has been measured on:
    # AMD 6376: n*4k-1; small n
    # AMD Neo N36L: 44k-200k
    # Intel i7-3632QM: 55k-
    # ARM Cortex A53: 4k-28k
    # Intel i5-2410M: 36k-46k
    #
    # I choose 2^15-1 = 32767
    # q{
    #	expseq() {
    #	    perl -E '
    #		$last = pop @ARGV;
    #	    $first = shift || 1;
    #	    $inc = shift || 1.03;
    #	    for($i=$first; $i<=$last;$i*=$inc) { say int $i }
    #	    ' "$@"
    #	}
    #
    #	seq 111111111 > big;
    #	f() { ppar --test $1 -a big --pipepart --block -1 'md5sum > /dev/null'; }
    #	export -f f;
    #	expseq 1000 1.001 300000 | shuf | parallel -j1 --jl jl-md5sum f;
    # };
    my $script = spacefree
	(0,
	 q{
	     while(@ARGV) {
		 sysseek(STDIN,shift,0) || die;
		 $left = shift;
		 while($read =
		       sysread(STDIN,$buf, $left > 32767 ? 32767 : $left)){
		     $left -= $read;
		     syswrite(STDOUT,$buf);
		 }
	     }
	 });
    return "<". Q($file) .
	" perl -e '$script' @start_len |";
}

sub column_perlexpr($$$) {
    # Compute the column number (if any), perlexpression from combined
    # string (such as --shard key, --groupby key, {=n perlexpr=}
    # Input:
    #	$column_perlexpr = string with column and perl expression
    #	$header = header from input file (if column is column name)
    #	$colsep = column separator regexp
    # Returns:
    #	$col = column number
    #	$perlexpr = perl expression
    #	$subref = compiled perl expression as sub reference
    my ($column_perlexpr, $header, $colsep) = @_;
    my ($col, $perlexpr, $subref);
    if($column_perlexpr =~ /^[-a-z0-9_]+(\s|$)/i) {
	# Column name/number (possibly prefix)
	if($column_perlexpr =~ s/^(-?\d+)(\s|$)//) {
	    # Column number (possibly prefix)
	    $col = $1;
	} elsif($column_perlexpr =~ s/^([a-z0-9_]+)(\s+|$)//i) {
	    # Column name (possibly prefix)
	    my $colname = $1;
	    # Split on --copsep pattern
	    my @headers = split /$colsep/, $header;
	    my %headers;
	    @headers{@headers} = (1..($#headers+1));
	    $col = $headers{$colname};
	    if(not defined $col) {
		::error("Column '$colname' $colsep not found in header",keys %headers);
		::wait_and_exit(255);
	    }
	}
    }
    # What is left of $column_perlexpr is $perlexpr (possibly empty)
    $perlexpr = $column_perlexpr;
    $subref = eval("sub { no strict; no warnings; $perlexpr }");
    return($col, $perlexpr, $subref);
}

sub group_by_loop($$) {
    # Generate perl code for group-by loop
    # Insert a $recsep when the column value changes
    # The column value can be computed with $perlexpr
    my($fh,$recsep) = @_;
    my $groupby = $opt::groupby;
    if($groupby =~ /^[a-z_][a-z_0-9]*(\s|$)/i) {
	# Group by column name
	# (Yes, this will also wrongly match a perlexpr like: chop)
	my($read,$char,@line);
	# Read a full line, but nothing more
	# (the rest must be read by the child)
	# $Global::header used to prepend block to each job
	do {
	    $read = sysread($fh,$char,1);
	    push @line, $char;
	} while($read and $char ne "\n");
	$Global::header = join "", @line;
    }
    $opt::colsep ||= "\t";
    ($group_by::col, $group_by::perlexpr, $group_by::subref) =
	column_perlexpr($groupby, $Global::header, $opt::colsep);
    # Numbered 0..n-1 due to being used by $F[n]
    if($group_by::col) { $group_by::col--; }

    my $loop = ::spacefree(0,q{
	BEGIN{ $last = "RECSEP"; }
	{
	    local $_=COLVALUE;
	    PERLEXPR;
	    if(($last) ne $_) {
		print "RECSEP";
		$last = $_;
	    }
	}
			   });
    if(defined $group_by::col) {
	$loop =~ s/COLVALUE/\$F[$group_by::col]/g;
    } else {
	$loop =~ s/COLVALUE/\$_/g;
    }
    $loop =~ s/PERLEXPR/$group_by::perlexpr/g;
    $loop =~ s/RECSEP/$recsep/g;
    return $loop;
}

sub pipe_group_by_setup() {
    # Record separator with 119 bit random value
    $opt::recend = '';
    $opt::recstart =
	join "", map { (0..9,"a".."z","A".."Z")[rand(62)] } (1..20);
    $opt::remove_rec_sep = 1;
    my @filter;
    push @filter, "perl";
    if($opt::groupby =~ /^[a-z0-9_]+(\s|$)/i) {
	# This is column number/name
	# Use -a (auto-split)
	push @filter, "-a";
	$opt::colsep ||= "\t";
	my $sep = $opt::colsep;
	$sep =~ s/\t/\\t/g;
	$sep =~ s/\"/\\"/g;
	# man perlrun: -Fpattern [...] You can't use literal whitespace
	$sep =~ s/ /\\040/g;
	push @filter, "-F$sep";
    }
    push @filter, "-pe";
    push @filter, group_by_loop(*STDIN,$opt::recstart);
    ::debug("init", "@filter\n");
    open(STDIN, '-|', @filter) || die ("Cannot start @filter");
    if(which("mbuffer")) {
	# You get a speed up of 30% by going through mbuffer
	open(STDIN, '-|', "mbuffer", "-q","-m6M","-b5") ||
	    die ("Cannot start mbuffer");
    }
}

sub spreadstdin() {
    # read a record
    # Spawn a job and print the record to it.
    # Uses:
    #	$Global::blocksize
    #	STDIN
    #	$opt::r
    #	$Global::max_lines
    #	$Global::max_number_of_args
    #	$opt::regexp
    #	$Global::start_no_new_jobs
    #	$opt::roundrobin
    #	%Global::running
    # Returns: N/A

    my $buf = "";
    my ($recstart,$recend) = recstartrecend();
    my $recendrecstart = $recend.$recstart;
    my $chunk_number = 1;
    my $one_time_through;
    my $two_gb = 2**31-1;
    my $blocksize = int($Global::blocksize);
    my $in = *STDIN;
    my $timeout = $Global::blocktimeout;

    if($opt::skip_first_line) {
	my $newline;
	# Read a full line one byte at a time
	while(sysread($in,$newline,1,0)) {
	    $newline eq "\n" and last;
	}
    }
    my $header = find_header(\$buf,$in);
    my $anything_written;
    my $eof;
    my $garbage_read;

    sub read_block() {
	# Read a --blocksize from STDIN
	# possibly interrupted by --blocktimeout
	# Add up to the next full block
	my $readsize = $blocksize - (length $buf) % $blocksize;
	my ($nread,$alarm);
	eval {
	    local $SIG{ALRM} = sub { die "alarm\n" }; # NB: \n required
	    # --blocktimeout (or 0 if not set)
	    alarm $timeout;
	    if($] >= 5.026) {
		do {
		    $nread = sysread $in, $buf, $readsize, length $buf;
		    $readsize -= $nread;
		} while($readsize and $nread);
	    } else {
		# Less efficient reading, but 32-bit sysread compatible
		do {
		    $nread = sysread($in,substr($buf,length $buf,0),$readsize,0);
		    $readsize -= $nread;
		} while($readsize and $nread);
	    }
	    alarm 0;
	};
	if ($@) {
	    die unless $@ eq "alarm\n";	  # propagate unexpected errors
	    $alarm = 1;
	} else {
	    $alarm = 0;
	}
	$eof = not ($nread or $alarm);
    }

    sub pass_n_line_records() {
	# Pass records of N lines
	my $n_lines = $buf =~ tr/\n/\n/;
	my $last_newline_pos = rindex64(\$buf,"\n");
	# Go backwards until there are full n-line records
	while($n_lines % $Global::max_lines) {
	    $n_lines--;
	    $last_newline_pos = rindex64(\$buf,"\n",$last_newline_pos-1);
	}
	# Chop at $last_newline_pos as that is where n-line record ends
	$anything_written +=
	    write_record_to_pipe($chunk_number++,\$header,\$buf,
				 $recstart,$recend,$last_newline_pos+1);
	shorten(\$buf,$last_newline_pos+1);
    }

    sub pass_n_regexps() {
	# Pass records of N regexps
	# -N => (start..*?end){n}
	# -L -N => (start..*?end){n*l}
	if(not $garbage_read) {
	    $garbage_read = 1;
	    if($buf !~ /^$recstart/o) {
		# Buf does not start with $recstart => There is garbage.
		# Make a single record of the garbage
		if($buf =~
		   /(?s:^)(
		   (?:(?:(?!$recend$recstart)(?s:.))*?$recend)
		   )
		   # Followed by recstart
		   (?=$recstart)/mox and length $1 > 0) {
		    $anything_written +=
			write_record_to_pipe($chunk_number++,\$header,\$buf,
					     $recstart,$recend,length $1);
		    shorten(\$buf,length $1);
		}
	    }
	}

	my $n_records =
	    $Global::max_number_of_args * ($Global::max_lines || 1);
	# (?!negative lookahead) is needed to avoid backtracking
	# See: https://unix.stackexchange.com/questions/439356/
	# (?s:.) = (.|[\n]) but faster
	while($buf =~
	      /(?s:^)(
	      # n more times recstart.*recend
	      (?:$recstart(?:(?!$recend$recstart)(?s:.))*?$recend){$n_records}
	      )
	      # Followed by recstart
	      (?=$recstart)/mox and length $1 > 0) {
	    $anything_written +=
		write_record_to_pipe($chunk_number++,\$header,\$buf,
				     $recstart,$recend,length $1);
	    shorten(\$buf,length $1);
	}
    }

    sub pass_regexp() {
	# Find the last recend-recstart in $buf
	$eof and return;
	# (?s:.) = (.|[\n]) but faster
	if($buf =~ /^((?s:.)*$recend)$recstart(?s:.)*?$/mox) {
	    $anything_written +=
		write_record_to_pipe($chunk_number++,\$header,\$buf,
				     $recstart,$recend,length $1);
	    shorten(\$buf,length $1);
	}
    }

    sub pass_csv_record() {
	# Pass CVS record
	# We define a CSV record as an even number of " + end of line
	# This works if you use " as quoting character
	my $last_newline_pos = length $buf;
	# Go backwards from the last \n and search for a position
	# where there is an even number of "
	do {
	    # find last EOL
	    $last_newline_pos = rindex64(\$buf,"\n",$last_newline_pos-1);
	    # While uneven "
	} while((substr($buf,0,$last_newline_pos) =~ y/"/"/)%2
		and $last_newline_pos >= 0);
	# Chop at $last_newline_pos as that is where CSV record ends
	$anything_written +=
	    write_record_to_pipe($chunk_number++,\$header,\$buf,
				 $recstart,$recend,$last_newline_pos+1);
	shorten(\$buf,$last_newline_pos+1);
    }

    sub pass_n() {
	# Pass n records of --recend/--recstart
	# -N => (start..*?end){n}
	my $i = 0;
	my $read_n_lines =
	    $Global::max_number_of_args * ($Global::max_lines || 1);
	    while(($i = nindex(\$buf,$recendrecstart,$read_n_lines)) != -1
		  and
		  length $buf) {
		$i += length $recend; # find the actual splitting location
		$anything_written +=
		    write_record_to_pipe($chunk_number++,\$header,\$buf,
					 $recstart,$recend,$i);
		shorten(\$buf,$i);
	    }
    }

    sub pass() {
	# Pass records of --recend/--recstart
	# Split record at fixed string
	# Find the last recend+recstart in $buf
	$eof and return;
	my $i = rindex64(\$buf,$recendrecstart);
	if($i != -1) {
	    $i += length $recend; # find the actual splitting location
	    $anything_written +=
		write_record_to_pipe($chunk_number++,\$header,\$buf,
				     $recstart,$recend,$i);
	    shorten(\$buf,$i);
	}
    }

    sub increase_blocksize_maybe() {
	if(not $anything_written
	   and not $opt::blocktimeout
	   and not $Global::no_autoexpand_block) {
	    # Nothing was written - maybe the block size < record size?
	    # Increase blocksize exponentially up to 2GB-1 (2GB causes problems)
	    if($blocksize < $two_gb) {
		my $old_blocksize = $blocksize;
		$blocksize = ::min(ceil($blocksize * 1.3 + 1), $two_gb);
		::warning("A record was longer than $old_blocksize. " .
			  "Increasing to --blocksize $blocksize.");
	    }
	}
    }

    while(1) {
	$anything_written = 0;
	read_block();
	if($opt::r) {
	    # Remove empty lines
	    $buf =~ s/^\s*\n//gm;
	    if(length $buf == 0) {
		if($eof) {
		    last;
		} else {
		    next;
		}
	    }
	}
	if($Global::max_lines and not $Global::max_number_of_args) {
	    # Pass n-line records
	    pass_n_line_records();
	} elsif($opt::csv) {
	    # Pass a full CSV record
	    pass_csv_record();
	} elsif($opt::regexp) {
	    # Split record at regexp
	    if($Global::max_number_of_args) {
		pass_n_regexps();
	    } else {
		pass_regexp();
	    }
	} else {
	    # Pass normal --recend/--recstart record
	    if($Global::max_number_of_args) {
		pass_n();
	    } else {
		pass();
	    }
	}
	$eof and last;
	increase_blocksize_maybe();
	::debug("init", "Round\n");
    }
    ::debug("init", "Done reading input\n");

    # If there is anything left in the buffer write it
    write_record_to_pipe($chunk_number++, \$header, \$buf, $recstart,
			 $recend, length $buf);

    if($opt::retries) {
	$Global::no_more_input = 1;
	# We need to start no more jobs: At most we need to retry some
	# of the already running.
	my @running = values %Global::running;
	# Stop any virgins.
	for my $job (@running) {
	    if(defined $job and $job->virgin()) {
		close $job->fh(0,"w");
	    }
	}
	# Wait for running jobs to be done
	my $sleep = 1;
	while($Global::total_running > 0) {
	    $sleep = ::reap_usleep($sleep);
	    start_more_jobs();
	}
    }
    $Global::start_no_new_jobs ||= 1;
    if($opt::roundrobin) {
	# Flush blocks to roundrobin procs
	my $sleep = 1;
	while(%Global::running) {
	    my $something_written = 0;
	    for my $job (values %Global::running) {
		if($job->block_length()) {
		    $something_written += $job->non_blocking_write();
		} else {
		    close $job->fh(0,"w");
		}
	    }
	    if($something_written) {
		$sleep = $sleep/2+0.001;
	    }
	    $sleep = ::reap_usleep($sleep);
	}
    }
}

sub recstartrecend() {
    # Uses:
    #	$opt::recstart
    #	$opt::recend
    # Returns:
    #	$recstart,$recend with default values and regexp conversion
    my($recstart,$recend);
    if(defined($opt::recstart) and defined($opt::recend)) {
	# If both --recstart and --recend is given then both must match
	$recstart = $opt::recstart;
	$recend = $opt::recend;
    } elsif(defined($opt::recstart)) {
	# If --recstart is given it must match start of record
	$recstart = $opt::recstart;
	$recend = "";
    } elsif(defined($opt::recend)) {
	# If --recend is given then it must match end of record
	$recstart = "";
	$recend = $opt::recend;
	if($opt::regexp and $recend eq '') {
	    # --regexp --recend ''
	    $recend = '(?s:.)';
	}
    }

    if($opt::regexp) {
	# Do not allow /x comments - to avoid having to quote space
	$recstart = "(?-x:".$recstart.")";
	$recend = "(?-x:".$recend.")";
	# If $recstart/$recend contains '|'
	# the | should only apply to the regexp
	$recstart = "(?:".$recstart.")";
	$recend = "(?:".$recend.")";
    } else {
	# $recstart/$recend = printf strings (\n)
	$recstart =~ s/\\([0rnt\'\"\\])/"qq|\\$1|"/gee;
	$recend =~ s/\\([0rnt\'\"\\])/"qq|\\$1|"/gee;
    }
    return ($recstart,$recend);
}

sub nindex($$) {
    # See if string is in buffer N times
    # Returns:
    #	the position where the Nth copy is found
    my ($buf_ref, $str, $n) = @_;
    my $i = 0;
    for(1..$n) {
	$i = index64($buf_ref,$str,$i+1);
	if($i == -1) { last }
    }
    return $i;
}

{
    my @robin_queue;
    my $sleep = 1;

    sub round_robin_write($$$$$) {
	# Input:
	#   $header_ref = ref to $header string
	#   $block_ref = ref to $block to be written
	#   $recstart = record start string
	#   $recend = record end string
	#   $endpos = end position of $block
	# Uses:
	#   %Global::running
	# Returns:
	#   $something_written = amount of bytes written
	my ($header_ref,$buffer_ref,$recstart,$recend,$endpos) = @_;
	my $written = 0;
	my $block_passed = 0;
	while(not $block_passed) {
	    # Continue flushing existing buffers
	    # until one is empty and a new block is passed
	    if(@robin_queue) {
		# Rotate queue once so new blocks get a fair chance
		# to be given to another slot
		push @robin_queue, shift @robin_queue;
	    } else {
		# Make a queue to spread the blocks evenly
		push @robin_queue, (sort { $a->seq() <=> $b->seq() }
				    values %Global::running);
	    }
	    do {
		$written = 0;
		for my $job (@robin_queue) {
		    if($job->block_length() > 0) {
			$written += $job->non_blocking_write();
		    } else {
			$job->set_block($header_ref, $buffer_ref,
					$endpos, $recstart, $recend);
			$block_passed = 1;
			$written += $job->non_blocking_write();
			last;
		    }
		}
		if($written) {
		    $sleep = $sleep/1.5+0.001;
		}
		# Don't sleep if something is written
	    } while($written and not $block_passed);
	    $sleep = ::reap_usleep($sleep);
	}
	return $written;
    }
}

sub index64($$$) {
    # Do index on strings > 2GB.
    # index in Perl < v5.22 does not work for > 2GB
    # Input:
    #	as index except STR which must be passed as a reference
    # Output:
    #	as index
    my $ref = shift;
    my $match = shift;
    my $pos = shift || 0;
    my $max2gb = 2**31-1;
    my $strlen = length($$ref);
    # No point in doing extra work if we don't need to.
    if($strlen < $max2gb or $] > 5.022) {
	return index($$ref, $match, $pos);
    }

    my $matchlen = length($match);
    my $ret;
    my $offset = $pos;
    while($offset < $strlen) {
	$ret = index(
	    substr($$ref, $offset, $max2gb),
	    $match, $pos-$offset);
	if($ret != -1) {
	    return $ret + $offset;
	}
	$offset += ($max2gb - $matchlen - 1);
    }
    return -1;
}

sub rindex64($@) {
    # Do rindex on strings > 2GB.
    # rindex in Perl < v5.22 does not work for > 2GB
    # Input:
    #	as rindex except STR which must be passed as a reference
    # Output:
    #	as rindex
    my $ref = shift;
    my $match = shift;
    my $pos = shift;
    my $block_size = 2**31-1;
    my $strlen = length($$ref);
    # Default: search from end
    $pos = defined $pos ? $pos : $strlen;
    # No point in doing extra work if we don't need to.
    if($strlen < $block_size or $] > 5.022) {
	return rindex($$ref, $match, $pos);
    }

    my $matchlen = length($match);
    my $ret;
    my $offset = $pos - $block_size + $matchlen;
    if($offset < 0) {
	# The offset is less than a $block_size
	# Set the $offset to 0 and
	# Adjust block_size accordingly
	$block_size = $block_size + $offset;
	$offset = 0;
    }
    while($offset >= 0) {
	$ret = rindex(
	    substr($$ref, $offset, $block_size),
	    $match);
	if($ret != -1) {
	    return $ret + $offset;
	}
	$offset -= ($block_size - $matchlen - 1);
    }
    return -1;
}

sub shorten($$) {
    # Do: substr($buf,0,$i) = "";
    # Some Perl versions do not support $i > 2GB, so do this in 2GB chunks
    # Input:
    #	$buf_ref = \$buf
    #	$i = position to shorten to
    # Returns: N/A
    my ($buf_ref, $i) = @_;
    my $two_gb = 2**31-1;
    while($i > $two_gb) {
	substr($$buf_ref,0,$two_gb) = "";
	$i -= $two_gb;
    }
    substr($$buf_ref,0,$i) = "";
}

sub write_record_to_pipe($$$$$$) {
    # Fork then
    # Write record from pos 0 .. $endpos to pipe
    # Input:
    #	$chunk_number = sequence number - to see if already run
    #	$header_ref = reference to header string to prepend
    #	$buffer_ref = reference to record to write
    #	$recstart = start string of record
    #	$recend = end string of record
    #	$endpos = position in $buffer_ref where record ends
    # Uses:
    #	$Global::job_already_run
    #	$opt::roundrobin
    #	@Global::virgin_jobs
    # Returns:
    #	Number of chunks written (0 or 1)
    my ($chunk_number, $header_ref, $buffer_ref,
	$recstart, $recend, $endpos) = @_;
    if($endpos == 0) { return 0; }
    if(vec($Global::job_already_run,$chunk_number,1)) { return 1; }
    if($opt::roundrobin) {
	# Write the block to one of the already running jobs
	return round_robin_write($header_ref, $buffer_ref,
				 $recstart, $recend, $endpos);
    }
    # If no virgin found, backoff
    my $sleep = 0.0001; # 0.01 ms - better performance on highend
    while(not @Global::virgin_jobs) {
	::debug("pipe", "No virgin jobs");
	$sleep = ::reap_usleep($sleep);
	# Jobs may not be started because of loadavg
	# or too little time between each ssh login
	# or retrying failed jobs.
	start_more_jobs();
    }
    my $job = shift @Global::virgin_jobs;
    $job->set_block($header_ref, $buffer_ref, $endpos, $recstart, $recend);
    $job->write_block();
    return 1;
}


sub __SEM_MODE__() {}


sub acquire_semaphore() {
    # Acquires semaphore. If needed: spawns to the background
    # Uses:
    #	@Global::host
    # Returns:
    #	The semaphore to be released when jobs is complete
    $Global::host{':'} = SSHLogin->new(":");
    my $sem = Semaphore->new($Semaphore::name,
			     $Global::host{':'}->max_jobs_running());
    $sem->acquire();
    if($Semaphore::fg) {
	# skip
    } else {
	if(fork()) {
	    exit(0);
	} else {
	    # If run in the background, the PID will change
	    $sem->pid_change();
	}
    }
    return $sem;
}


sub __PARSE_OPTIONS__() {}

sub shell_completion() {
    if($opt::shellcompletion eq "zsh") {
	# if shell == zsh
	zsh_competion();
    } elsif($opt::shellcompletion eq "bash") {
	# if shell == bash
	bash_competion();
    } elsif($opt::shellcompletion eq "auto") {
	if($Global::shell =~ m:/zsh$|^zsh$:) {
	    # if shell == zsh
	    zsh_competion();
	} elsif($Global::shell =~ m:/bash$|^bash$:) {
	    # if shell == bash
	    bash_competion();
	} else {
	    ::error("--shellcompletion is not implemented for ".
		    "'$Global::shell'.");
	    wait_and_exit(255);
	}
    } else {
	::error("--shellcompletion is not implemented for ".
		"'$opt::shellcompletion'.");
	wait_and_exit(255);
    }
}

sub bash_competion() {
    # Print:
    #   complete -F _comp_parallel parallel;
    #   _comp_parallel() {
    #     COMPREPLY=($(compgen -W "--options" --
    #                    "${COMP_WORDS[$COMP_CWORD]}"));
    #   };
    my @bash_completion =
	("complete -F _comp_parallel parallel;",
	 '_comp_parallel() { COMPREPLY=($(compgen -W "');
    my @och = options_completion_hash();
    while(@och) {
	$_ = shift @och;
	# Split input like:
	# "joblog|jl=s[Logfile for executed jobs]:logfile:_files"
	if(/^(.*?)(\[.*?])?(:[^:]*)?(:.*)?$/) {
	    my $opt = $1;
	    my $desc = $2;
	    my $argdesc = $3;
	    my $func = $4;
	    # opt=s => opt
	    $opt =~ s/[:=].$//;
	    if($opt =~ /^_/) {
		# internal options start with --_
		# skip
	    } else {
		push @bash_completion,
		    (map { (length $_ == 1) ? "-$_ " : "--$_ " }
		     split /\|/, $opt);
	    }
	}
	shift @och;
    }
    push @bash_completion,'" -- "${COMP_WORDS[$COMP_CWORD]}")); };'."\n";
    print @bash_completion;
}

sub zsh_competion() {
    # Print code used for completion in zsh
    my @zsh_completion =
	("compdef _comp_parallel parallel; ",
	 "setopt localoptions extended_glob; ",
	 "_comp_parallel() { ",
	 "_arguments ");
    my @och = options_completion_hash();
    while(@och) {
	$_ = shift @och;
	# Split input like:
	# "joblog|jl=s[Logfile for executed jobs]:logfile:_files"
	if(/^(.*?)(\[.*?])?(:[^:]*)?(:.*)?$/) {
	    my $opt = $1;
	    my $desc = $2;
	    my $argdesc = $3;
	    my $func = $4;
	    # opt=s => opt
	    $opt =~ s/[:=].$//;
	    if($opt =~ /^_/) {
		# internal options start with --_
		# skip
	    } else {
		# {-o,--option}
		my $zsh_opt = join(",",
				   (map { (length $_ == 1) ? "-$_" : "--$_" }
				    split /\|/, $opt));
		if($zsh_opt =~ /,/) { $zsh_opt = "{$zsh_opt}"; }
		$desc =~ s/'/'"'"'/g;
		$argdesc =~ s/'/'"'"'/g;
		$func =~ s/'/'"'"'/g;
		push @zsh_completion, $zsh_opt."'".$desc.$argdesc.$func."' ";
	    }
	}
	shift @och;
    }
    push @zsh_completion,
	q{'(-)1:command:{_command_names -e}' },
	q{'*::arguments:_normal'},
	"};\n";
    print @zsh_completion;
}

sub options_hash() {
    # Returns:
    #	%hash = for GetOptions
    my %och = options_completion_hash();
    my %oh;
    my ($k,$v);
    while(($k,$v) = each %och) {
	# Remove description
	$k =~ s/\[.*//;
	$oh{$k} = $v;
    }
    return %oh;
}

sub options_completion_hash() {
    # Returns:
    #	%hash = for GetOptions and shell completion
    return
	("debug|D=s" => \$opt::D,
	 "xargs[Insert as many arguments as the command line length permits]"
	 => \$opt::xargs,
	 "m[Multiple arguments]" => \$opt::m,
	 ("X[Insert as many arguments with context as the command line ".
	 "length permits]"
	 => \$opt::X),
	 "v[Verbose]" => \@opt::v,
	 "sql=s[Use --sql-master instead (obsolete)]:DBURL" => \$opt::retired,
	 ("sql-master|sqlmaster=s".
	  "[Submit jobs via SQL server. DBURL must point to a table, which ".
	  "will contain --joblog, the values, and output]:DBURL"
	  => \$opt::sqlmaster),
	 ("sql-worker|sqlworker=s".
	  "[Execute jobs via SQL server. Read the input sources variables ".
	  "from the table pointed to by DBURL.]:DBURL"
	  => \$opt::sqlworker),
	 ("sql-and-worker|sqlandworker=s".
	  "[--sql-master DBURL --sql-worker DBURL]:DBURL"
	  => \$opt::sqlandworker),
	 ("joblog|jl=s[Logfile for executed jobs]:logfile:_files"
	  => \$opt::joblog),
	 ("results|result|res=s[Save the output into files]:name:_files"
	  => \$opt::results),
	 "resume[Resumes from the last unfinished job]" => \$opt::resume,
	 ("resume-failed|resumefailed".
	  "[Retry all failed and resume from the last unfinished job]"
	  => \$opt::resume_failed),
	 ("retry-failed|retryfailed[Retry all failed jobs in joblog]"
	  => \$opt::retry_failed),
	 "silent[Silent]" => \$opt::silent,
	 ("keep-order|keeporder|k".
	  "[Keep sequence of output same as the order of input]"
	  => \$opt::keeporder),
	 ("no-keep-order|nokeeporder|nok|no-k".
	  "[Overrides an earlier --keep-order (e.g. if set in ".
	  "~/.parallel/config)]"
	  => \$opt::nokeeporder),
	 "group[Group output]" => \$opt::group,
	 "g" => \$opt::retired,
	 ("ungroup|u".
	  "[Output is printed as soon as possible and bypasses GNU parallel ".
	  "internal processing]"
	  => \$opt::ungroup),
	 ("latest-line|latestline|ll".
	  "[Print latest line of each job]"
	  => \$opt::latestline),
	 ("line-buffer|line-buffered|linebuffer|linebuffered|lb".
	  "[Buffer output on line basis]"
	  => \$opt::linebuffer),
	 ("tmux".
	  "[Use tmux for output. Start a tmux session and run each job in a ".
	  "window in that session. No other output will be produced]"
	  => \$opt::tmux),
	 ("tmux-pane|tmuxpane".
	  "[Use tmux for output but put output into panes in the first ".
	  "window.  Useful if you want to monitor the progress of less than ".
	  "100 concurrent jobs]"
	  => \$opt::tmuxpane),
	 "null|0[Use NUL as delimiter]" => \$opt::null,
	 "quote|q[Quote command]" => \$opt::quote,
	 # Replacement strings
	 ("parens=s[Use parensstring instead of {==}]:parensstring"
	  => \$opt::parens),
	 ('rpl=s[Define replacement string]:"tag perl expression"'
	  => \@opt::rpl),
	 "plus[Add more replacement strings]" => \$opt::plus,
	 ("I=s".
	  "[Use the replacement string replace-str instead of {}]:replace-str"
	  => \$opt::I),
	 ("extensionreplace|er=s".
	  "[Use the replacement string replace-str instead of {.} for input ".
	  "line without extension]:replace-str"
	  => \$opt::U),
	 "U=s" => \$opt::retired,
	 ("basenamereplace|bnr=s".
	  "[Use the replacement string replace-str instead of {/} for ".
	  "basename of input line]:replace-str"
	  => \$opt::basenamereplace),
	 ("dirnamereplace|dnr=s".
	  "[Use the replacement string replace-str instead of {//} for ".
	  "dirname of input line]:replace-str"
	  => \$opt::dirnamereplace),
	 ("basenameextensionreplace|bner=s".
	  "[Use the replacement string replace-str instead of {/.} for ".
	  "basename of input line without extension]:replace-str"
	  => \$opt::basenameextensionreplace),
	 ("seqreplace=s".
	  "[Use the replacement string replace-str instead of {#} for job ".
	  "sequence number]:replace-str"
	  => \$opt::seqreplace),
	 ("slotreplace=s".
	  "[Use the replacement string replace-str instead of {%} for job ".
	  "slot number]:replace-str"
	  => \$opt::slotreplace),
	 ("delay=s".
	  "[Delay starting next job by duration]:duration" => \$opt::delay),
	 ("ssh-delay|sshdelay=f".
	  "[Delay starting next ssh by duration]:duration"
	  => \$opt::sshdelay),
	 ("load=s".
	  "[Only start jobs if load is less than max-load]:max-load"
	  => \$opt::load),
	 "noswap[Do not start job is computer is swapping]" => \$opt::noswap,
	 ("max-line-length-allowed|maxlinelengthallowed".
	  "[Print maximal command line length]"
	  => \$opt::max_line_length_allowed),
	 ("number-of-cpus|numberofcpus".
	  "[Print the number of physical CPU cores and exit (obsolete)]"
	  => \$opt::number_of_cpus),
	 ("number-of-sockets|numberofsockets".
	  "[Print the number of CPU sockets and exit]"
	  => \$opt::number_of_sockets),
	 ("number-of-cores|numberofcores".
	  "[Print the number of physical CPU cores and exit]"
	  => \$opt::number_of_cores),
	 ("number-of-threads|numberofthreads".
	  "[Print the number of hyperthreaded CPU cores and exit]"
	  => \$opt::number_of_threads),
	 ("use-sockets-instead-of-threads|usesocketsinsteadofthreads".
	  "[Determine how GNU Parallel counts the number of CPUs]"
	  => \$opt::use_sockets_instead_of_threads),
	 ("use-cores-instead-of-threads|usecoresinsteadofthreads".
	  "[Determine how GNU Parallel counts the number of CPUs]"
	  => \$opt::use_cores_instead_of_threads),
	 ("use-cpus-instead-of-cores|usecpusinsteadofcores".
	  "[Determine how GNU Parallel counts the number of CPUs]"
	  => \$opt::use_cpus_instead_of_cores),
	 ("shell-quote|shellquote|shell_quote".
	  "[Does not run the command but quotes it. Useful for making ".
	  "quoted composed commands for GNU parallel]"
	  => \@opt::shellquote),
	 ('nice=i[Run the command at this niceness]:niceness:($(seq -20 19))'
	  => \$opt::nice),
	 "tag[Tag lines with arguments]" => \$opt::tag,
	 ("tag-string|tagstring=s".
	  "[Tag lines with a string]:str" => \$opt::tagstring),
	 "ctag[Color tag]:str" => \$opt::ctag,
	 "ctag-string|ctagstring=s[Colour tagstring]:str" => \$opt::ctagstring,
	 "color|colour[Colourize output]" => \$opt::color,
	 ("color-failed|colour-failed|colorfailed|colourfailed|".
	  "color-fail|colour-fail|colorfail|colourfail|cf".
	  "[Colour failed jobs red]"
	  => \$opt::colorfailed),
	 ("onall[Run all the jobs on all computers given with --sshlogin]"
	  => \$opt::onall),
	 "nonall[--onall with no arguments]" => \$opt::nonall,
	 ("filter-hosts|filterhosts|filter-host[Remove down hosts]"
	  => \$opt::filter_hosts),
	 ('sshlogin|S=s'.
	  '[Distribute jobs to remote computers]'.
	  ':[@hostgroups/][ncpus/]sshlogin'.
	  '[,[@hostgroups/][ncpus/]sshlogin[,...]] or @hostgroup'.
	  ':_users') => \@opt::sshlogin,
	 ("sshloginfile|slf=s".
	  "[File with sshlogins on separate lines. Lines starting with '#' ".
	  "are ignored.]:filename:_files"
	  => \@opt::sshloginfile),
	 ("controlmaster|M".
	  "[Use ssh's ControlMaster to make ssh connections faster]"
	  => \$opt::controlmaster),
	 ("ssh=s".
	  "[Use this command instead of ssh for remote access]:sshcommand"
	  => \$opt::ssh),
	 ("transfer-file|transferfile|transfer-files|transferfiles|tf=s".
	  "[Transfer filename to remote computers]:filename:_files"
	  => \@opt::transfer_files),
	 ("return=s[Transfer files from remote computers]:filename:_files"
	  => \@opt::return),
	 ("trc=s[--transfer --return filename --cleanup]:filename:_files"
	  => \@opt::trc),
	 "transfer[Transfer files to remote computers]" => \$opt::transfer,
	 "cleanup[Remove transferred files]" => \$opt::cleanup,
	 ("basefile|bf=s".
	  "[Transfer file to each sshlogin before first job is started]".
	  ":file:_files"
	  => \@opt::basefile),
	 ("template|tmpl=s".
	  "[Replace replacement strings in file and save it in repl]".
	  ":file=repl:_files"
	  => \%opt::template),
	 "B=s" => \$opt::retired,
	 "ctrl-c|ctrlc" => \$opt::retired,
	 "no-ctrl-c|no-ctrlc|noctrlc" => \$opt::retired,
	 ("work-dir|workdir|wd=s".
	  "[Jobs will be run in the dir mydir. (default: the current dir ".
	  "for the local machine, the login dir for remote computers)]".
	  ":mydir:_cd"
	  => \$opt::workdir),
	 "W=s" => \$opt::retired,
	 ("rsync-opts|rsyncopts=s[Options to pass on to rsync]:options"
	  => \$opt::rsync_opts),
	 ("tmpdir|tempdir=s[Directory for temporary files]:dirname:_cd"
	  => \$opt::tmpdir),
	 ("use-compress-program|compress-program|".
	  "usecompressprogram|compressprogram=s".
	  "[Use prg for compressing temporary files]:prg:_commands"
	  => \$opt::compress_program),
	 ("use-decompress-program|decompress-program|".
	  "usedecompressprogram|decompressprogram=s".
	  "[Use prg for decompressing temporary files]:prg:_commands"
	  => \$opt::decompress_program),
	 "compress[Compress temporary files]" => \$opt::compress,
	 "open-tty|o[Open terminal tty]" => \$opt::open_tty,
	 "tty[Open terminal tty]" => \$opt::tty,
	 "T" => \$opt::retired,
	 "H=i" => \$opt::retired,
	 ("dry-run|dryrun|dr".
	  "[Print the job to run on stdout (standard output), but do not ".
	  "run the job]"
	  => \$opt::dryrun),
	 "progress[Show progress of computations]" => \$opt::progress,
	 ("eta[Show the estimated number of seconds before finishing]"
	  => \$opt::eta),
	 "bar[Show progress as a progress bar]" => \$opt::bar,
	 ("total-jobs|totaljobs|total=s".
	  "[Set total number of jobs]" => \$opt::totaljobs),
	 "shuf[Shuffle jobs]" => \$opt::shuf,
	 ("arg-sep|argsep=s".
	  "[Use sep-str instead of ::: as separator string]:sep-str"
	  => \$opt::arg_sep),
	 ("arg-file-sep|argfilesep=s".
	  "[Use sep-str instead of :::: as separator string ".
	  "between command and argument files]:sep-str"
	  => \$opt::arg_file_sep),
	 ('trim=s[Trim white space in input]:trim_method:'.
	  '((n\:"No trim" l\:"Left\ trim" r\:"Right trim" '.
	  'lr\:"Both trim" rl\:"Both trim"))'
	  => \$opt::trim),
	 "env=s[Copy environment variable var]:var:_vars" => \@opt::env,
	 "recordenv|record-env[Record environment]" => \$opt::record_env,
	 ('session'.
	  '[Record names in current environment in $PARALLEL_IGNORED_NAMES '.
	  'and exit. Only used with env_parallel. '.
	  'Aliases, functions, and variables with names i]'
	  => \$opt::session),
	 ('plain[Ignore --profile, $PARALLEL, and ~/.parallel/config]'
	  => \$opt::plain),
	 ("profile|J=s".
	  "[Use profile profilename for options]:profilename:_files"
	  => \@opt::profile),
	 "tollef" => \$opt::tollef,
	 "gnu[Behave like GNU parallel]" => \$opt::gnu,
	 "link|xapply[Link input sources]" => \$opt::link,
	 "linkinputsource|xapplyinputsource=i" => \@opt::linkinputsource,
	 # Before changing these lines, please read
	 # https://www.gnu.org/software/parallel/parallel_design.html#citation-notice
	 # https://git.savannah.gnu.org/cgit/parallel.git/tree/doc/citation-notice-faq.txt
	 # You accept to be put in a public hall-of-shame by removing
	 # these lines
	 ("bibtex|citation".
	  "[Print the citation notice and BibTeX entry for GNU parallel, ".
	  "silence citation notice for all future runs, and exit. ".
	  "It will not run any commands]"
	  => \$opt::citation),
	 "will-cite|willcite|nn|nonotice|no-notice" => \$opt::willcite,
	 # Termination and retries
	 ('halt-on-error|haltonerror|halt=s'.
	  '[When should GNU parallel terminate]'.
	  ':when:((now\:"kill all running jobs and halt immediately" '.
	  'soon\:"wait for all running jobs to complete, start no new jobs"))'
	  => \$opt::halt),
	 'limit=s[Dynamic job limit]:"command args"' => \$opt::limit,
	 ("memfree=s".
	  "[Minimum memory free when starting another job]:size"
	  => \$opt::memfree),
	 ("memsuspend=s".
	  "[Suspend jobs when there is less memory available]:size"
	  => \$opt::memsuspend),
	 "retries=s[Try failing jobs n times]:n" => \$opt::retries,
	 ("timeout=s".
	  "[Time out for command. If the command runs for longer than ".
	  "duration seconds it will get killed as per --term-seq]:duration"
	  => \$opt::timeout),
	 ("term-seq|termseq=s".
	  "[Termination sequence]:sequence" => \$opt::termseq),
	 # xargs-compatibility - implemented, man, testsuite
	 ("max-procs|maxprocs|P|jobs|j=s".
	  "[Add N to/Subtract N from/Multiply N% with/ the number of CPU ".
	  "threads or read parameter from file]:+N/-N/N%/N/procfile:_files"
	  => \$opt::jobs),
	 ("delimiter|d=s[Input items are terminated by delim]:delim"
	  => \$opt::d),
	 ("max-chars|maxchars|s=s[Limit length of command]:max-chars"
	  => \$opt::max_chars),
	 ("arg-file|argfile|a=s".
	  "[Use input-file as input source]:input-file:_files" => \@opt::a),
	 "no-run-if-empty|norunifempty|r[Do not run empty input]" => \$opt::r,
	 ("replace|i:s".
	  "[This option is deprecated; use -I instead]:replace-str"
	  => \$opt::i),
	 "E=s" => \$opt::eof,
	 ("eof|e:s[Set the end of file string to eof-str]:eof-str"
	  => \$opt::eof),
	 ("process-slot-var|processslotvar=s".
	  "[Set this variable to job slot number]:varname"
	  => \$opt::process_slot_var),
	 ("max-args|maxargs|n=s".
	  "[Use at most max-args arguments per command line]:max-args"
	  => \$opt::max_args),
	 ("max-replace-args|maxreplaceargs|N=s".
	  "[Use at most max-args arguments per command line]:max-args"
	  => \$opt::max_replace_args),
	 "col-sep|colsep|C=s[Column separator]:regexp" => \$opt::colsep,
	 "csv[Treat input as CSV-format]"=> \$opt::csv,
	 ("help|h[Print a summary of the options to GNU parallel and exit]"
	  => \$opt::help),
	 ("L=s[When used with --pipe: Read records of recsize]:recsize"
	  => \$opt::L),
	 ("max-lines|maxlines|l:f".
	  "[When used with --pipe: Read records of recsize lines]:recsize"
	  => \$opt::max_lines),
	 "interactive|p[Ask user before running a job]" => \$opt::interactive,
	 ("verbose|t[Print the job to be run on stderr (standard error)]"
	  => \$opt::verbose),
	 ("version|V[Print the version GNU parallel and exit]"
	  => \$opt::version),
	 ('min-version|minversion=i'.
	  '[Print the version GNU parallel and exit]'.
	  ':version:($(parallel --minversion 0))'
	  => \$opt::minversion),
	 ("show-limits|showlimits".
	  "[Display limits given by the operating system]"
	  => \$opt::show_limits),
	 ("exit|x[Exit if the size (see the -s option) is exceeded]"
	  => \$opt::x),
	 # Semaphore
	 "semaphore[Work as a counting semaphore]" => \$opt::semaphore,
	 ("semaphore-timeout|semaphoretimeout|st=s".
	  "[If secs > 0: If the semaphore is not released within secs ".
	  "seconds, take it anyway]:secs"
	  => \$opt::semaphoretimeout),
	 ("semaphore-name|semaphorename|id=s".
	  "[Use name as the name of the semaphore]:name"
	  => \$opt::semaphorename),
	 "fg[Run command in foreground]" => \$opt::fg,
	 "bg[Run command in background]" => \$opt::bg,
	 "wait[Wait for all commands to complete]" => \$opt::wait,
	 # Shebang #!/usr/bin/parallel --shebang
	 ("shebang|hashbang".
	  "[GNU parallel can be called as a shebang (#!) command as the ".
	  "first line of a script. The content of the file will be treated ".
	  "as inputsource]"
	  => \$opt::shebang),
	 ("_pipe-means-argfiles[internal]"
	  => \$opt::_pipe_means_argfiles),
	 "Y" => \$opt::retired,
	 ("skip-first-line|skipfirstline".
	  "[Do not use the first line of input]"
	  => \$opt::skip_first_line),
	 "_bug" => \$opt::_bug,
	 "_unsafe" => \$opt::_unsafe,
	 # --pipe
	 ("pipe|spreadstdin".
	  "[Spread input to jobs on stdin (standard input)]" => \$opt::pipe),
	 ("round-robin|roundrobin|round".
	  "[Distribute chunks of standard input in a round robin fashion]"
	  => \$opt::roundrobin),
	 "recstart=s" => \$opt::recstart,
	 ("recend=s".
	  "[Split record between endstring and startstring]:endstring"
	  => \$opt::recend),
	 ("regexp|regex".
	  "[Interpret --recstart and --recend as regular expressions]"
	  => \$opt::regexp),
	 ("remove-rec-sep|removerecsep|rrs".
	  "[Remove record separator]" => \$opt::remove_rec_sep),
	 ("output-as-files|outputasfiles|files[Save output to files]"
	  => \$opt::files),
	 ("output-as-files0|outputasfiles0|files0".
	  "[Save output to files separated by NUL]"
	  => \$opt::files0),
	 ("block-size|blocksize|block=s".
	  "[Size of block in bytes to read at a time]:size"
	  => \$opt::blocksize),
	 ("block-timeout|blocktimeout|bt=s".
	  "[Timeout for reading block when using --pipe]:duration"
	  => \$opt::blocktimeout),
	 "header=s[Use regexp as header]:regexp" => \$opt::header,
	 "cat[Create a temporary file with content]" => \$opt::cat,
	 "fifo[Create a temporary fifo with content]" => \$opt::fifo,
	 ("pipe-part|pipepart[Pipe parts of a physical file]"
	  => \$opt::pipepart),
	 "tee[Pipe all data to all jobs]" => \$opt::tee,
	 ("shard=s".
	  "[Use shardexpr as shard key and shard input to the jobs]:shardexpr"
	  => \$opt::shard),
	 ("bin=s".
	  "[Use binexpr as binning key and bin input to the jobs]:binexpr"
	  => \$opt::bin),
	 "group-by|groupby=s[Group input by value]:val" => \$opt::groupby,
	 #
	 ("hgrp|hostgrp|hostgroup|hostgroups[Enable hostgroups on arguments]"
	  => \$opt::hostgroups),
	 "embed[Embed GNU parallel in a shell script]" => \$opt::embed,
	 ("filter=s[Only run jobs where filter is true]:filter"
	  => \@opt::filter),
	 "_parset=s[Generate shell code for parset]" => \$opt::_parset,
	 ("shell-completion|shellcompletion=s".
	  "[Generate shell code for shell completion]:shell:(bash zsh)"
	  => \$opt::shellcompletion),
	 # Parameter for testing optimal values
	 "_test=s" => \$opt::_test,
	);
}

sub get_options_from_array($@) {
    # Run GetOptions on @array
    # Input:
    #	$array_ref = ref to @ARGV to parse
    #	@keep_only = Keep only these options (e.g. --profile)
    # Uses:
    #	@ARGV
    # Returns:
    #	true if parsing worked
    #	false if parsing failed
    #	@$array_ref is changed
    my ($array_ref, @keep_only) = @_;
    if(not @$array_ref) {
	# Empty array: No need to look more at that
	return 1;
    }
    # A bit of shuffling of @ARGV needed as GetOptionsFromArray is not
    # supported everywhere
    my @save_argv;
    my $this_is_ARGV = (\@::ARGV == $array_ref);
    if(not $this_is_ARGV) {
	@save_argv = @::ARGV;
	@::ARGV = @{$array_ref};
    }
    # If @keep_only set: Ignore all values except @keep_only
    my %options = options_hash();
    if(@keep_only) {
	my (%keep,@dummy);
	@keep{@keep_only} = @keep_only;
	for my $k (grep { not $keep{$_} } keys %options) {
	    # Store the value of the option in @dummy
	    $options{$k} = \@dummy;
	}
    }
    my $retval = GetOptions(%options);
    if(not $this_is_ARGV) {
	@{$array_ref} = @::ARGV;
	@::ARGV = @save_argv;
    }
    return $retval;
}

sub parse_parset() {
    $Global::progname = "parset";
    @Global::parset_vars = split /[ ,]/, $opt::_parset;
    my $var_or_assoc = shift @Global::parset_vars;
    # Legal names: var _v2ar arrayentry[2]
    my @illegal = (grep { not /^[a-zA-Z_][a-zA-Z_0-9]*(\[\d+\])?$/ }
		   @Global::parset_vars);
    if(@illegal) {
	::error
	    ("@illegal is an invalid variable name.",
	     "Variable names must be letter followed by letters or digits.",
	     "Usage:",
	     "  parset varname GNU Parallel options and command");
	wait_and_exit(255);
    }
    if($var_or_assoc eq "assoc") {
	my $var = shift @Global::parset_vars;
	print "$var=(";
	$Global::parset = "assoc";
	$Global::parset_endstring=")\n";
    } elsif($var_or_assoc eq "var") {
	if($#Global::parset_vars > 0) {
	    $Global::parset = "var";
	} else {
	    my $var = shift @Global::parset_vars;
	    print "$var=(";
	    $Global::parset = "array";
	    $Global::parset_endstring=")\n";
	}
    } else {
	::die_bug("parset: unknown '$opt::_parset'");
    }
}

sub parse_options(@) {
    # Returns: N/A
    init_globals();
    my @argv_before = @ARGV;
    @ARGV = read_options();

    # Before changing these line, please read
    # https://www.gnu.org/software/parallel/parallel_design.html#citation-notice
    # https://git.savannah.gnu.org/cgit/parallel.git/tree/doc/citation-notice-faq.txt
    # You accept to be added to a public hall-of-shame by removing the lines
    if(defined $opt::citation) {
	citation(\@argv_before,\@ARGV);
	wait_and_exit(0);
    }
    # no-* overrides *
    if($opt::nokeeporder) { $opt::keeporder = undef; }

    if(@opt::v) { $Global::verbose = $#opt::v+1; } # Convert -v -v to v=2
    if($opt::_bug) { ::die_bug("test-bug"); }
    $Global::debug = $opt::D;
    #
    ## Shell
    #
    $Global::shell = $ENV{'PARALLEL_SHELL'} || parent_shell($$)
	|| $ENV{'SHELL'} || "/bin/sh";
    if(not -x $Global::shell and not which($Global::shell)) {
	::error("Shell '$Global::shell' not found.");
	wait_and_exit(255);
    }
    ::debug("init","Global::shell $Global::shell\n");
    $Global::cshell = $Global::shell =~ m:(/[-a-z]*)?csh:;
    $Global::fish = $Global::shell =~ m:(/[-a-z]*)?fish:;
    if(defined $opt::_parset) { parse_parset(); }
    if(defined $opt::X) { $Global::ContextReplace = 1; }
    if(defined $opt::silent) { $Global::verbose = 0; }
    if(defined $opt::null) { $/ = "\0"; }
    if(defined $opt::files) { $Global::files = 1; $Global::files_sep = "\n"; }
    if(defined $opt::files0) { $Global::files = 1; $Global::files_sep = "\0"; }
    if(defined $opt::d) { $/ = unquote_printf($opt::d) }
    parse_replacement_string_options();
    $opt::tag ||= $opt::ctag;
    $opt::tagstring ||= $opt::ctagstring;
    if(defined $opt::ctag or defined $opt::ctagstring
	or defined $opt::color) {
	$Global::color = 1;
    }
    if($opt::linebuffer or $opt::latestline) {
	$Global::linebuffer = 1;
	Job::latestline_init();
    }
    if(defined $opt::tag and not defined $opt::tagstring) {
	# Default = {}
	$opt::tagstring = $Global::parensleft.$Global::parensright;
    }
    if(defined $opt::tagstring) {
	$opt::tagstring = unquote_printf($opt::tagstring);
	if($opt::tagstring =~
	   /\Q$Global::parensleft\E.*\S+.*\Q$Global::parensright\E/
	   and
	   $Global::linebuffer) {
	    # --tagstring contains {= ... =} and --linebuffer =>
	    #	recompute replacement string for each use (do not cache)
	    $Global::cache_replacement_eval = 0;
	}
    }
    if(defined $opt::interactive) { $Global::interactive = $opt::interactive; }
    if(defined $opt::quote) { $Global::quoting = 1; }
    if(defined $opt::r) { $Global::ignore_empty = 1; }
    if(defined $opt::verbose) { $Global::stderr_verbose = 1; }
    if(defined $opt::eof) { $Global::end_of_file_string = $opt::eof; }
    if(defined $opt::max_args) {
	$opt::max_args = multiply_binary_prefix($opt::max_args);
	$Global::max_number_of_args = $opt::max_args;
	if($opt::pipepart and $opt::groupby) { $Global::max_number_of_args = 1; }
    }
    if(defined $opt::blocktimeout) {
	$Global::blocktimeout = int(multiply_time_units($opt::blocktimeout));
	if($Global::blocktimeout < 1) {
	    ::error("--block-timeout must be at least 1");
	    wait_and_exit(255);
	}
    }
    if(defined $opt::timeout) {
	$Global::timeoutq = TimeoutQueue->new($opt::timeout);
    }
    if(defined $opt::tmpdir) { $ENV{'TMPDIR'} = $opt::tmpdir; }
    $ENV{'PARALLEL_RSYNC_OPTS'} = $opt::rsync_opts ||
	$ENV{'PARALLEL_RSYNC_OPTS'} || '-rlDzR';
    # Default: Same nice level as GNU  Parallel is started at
    $opt::nice ||= eval { getpriority(0,0) } || 0;
    if(defined $opt::help) { usage(); exit(0); }
    if(defined $opt::shellcompletion) { shell_completion(); exit(0); }
    if(defined $opt::embed) { embed(); exit(0); }
    if(defined $opt::sqlandworker) {
	$opt::sqlmaster = $opt::sqlworker = $opt::sqlandworker;
    }
    if(defined $opt::tmuxpane) { $opt::tmux = $opt::tmuxpane; }
    if(defined $opt::colsep) { $Global::trim = 'lr'; }
    if(defined $opt::csv) {
	if(not $Global::use{"Text::CSV"} ||= eval "use Text::CSV; 1;") {
	    ::error("The perl module Text::CSV is not installed.");
	    ::error("Try installing libtext-csv-perl or perl-Text-CSV.");
	    wait_and_exit(255);
	}
	$opt::colsep = defined $opt::colsep ? $opt::colsep : ",";
	my $csv_setting = { binary => 1, sep_char => $opt::colsep };
	my $sep = $csv_setting->{sep_char};
	$Global::csv = Text::CSV->new($csv_setting)
	    or die "Cannot use CSV: ".Text::CSV->error_diag ();
    }
    if(defined $opt::header) {
	$opt::colsep = defined $opt::colsep ? $opt::colsep : "\t";
    }
    if(defined $opt::trim) { $Global::trim = $opt::trim; }
    if(defined $opt::arg_sep) { $Global::arg_sep = $opt::arg_sep; }
    if(defined $opt::arg_file_sep) {
	$Global::arg_file_sep = $opt::arg_file_sep;
    }
    if(not defined $opt::process_slot_var) {
	$opt::process_slot_var = 'PARALLEL_JOBSLOT0';
    }
    if(defined $opt::number_of_sockets) {
	print SSHLogin::no_of_sockets(),"\n"; wait_and_exit(0);
    }
    if(defined $opt::number_of_cpus) {
	print SSHLogin::no_of_cores(),"\n"; wait_and_exit(0);
    }
    if(defined $opt::number_of_cores) {
	print SSHLogin::no_of_cores(),"\n"; wait_and_exit(0);
    }
    if(defined $opt::number_of_threads) {
	print SSHLogin::no_of_threads(),"\n"; wait_and_exit(0);
    }
    if(defined $opt::max_line_length_allowed) {
	print Limits::Command::real_max_length(),"\n"; wait_and_exit(0);
    }
    if(defined $opt::max_chars) {
	$opt::max_chars = multiply_binary_prefix($opt::max_chars);
    }
    if(defined $opt::version) { version(); wait_and_exit(0); }
    if(defined $opt::record_env) { record_env(); wait_and_exit(0); }
    if(@opt::sshlogin) { @Global::sshlogin = @opt::sshlogin; }
    if(@opt::sshloginfile) { read_sshloginfiles(@opt::sshloginfile); }
    if(@opt::return) { push @Global::ret_files, @opt::return; }
    if($opt::transfer) {
	push @Global::transfer_files, $opt::i || $opt::I || "{}";
    }
    push @Global::transfer_files, @opt::transfer_files;
    if(%opt::template) {
	while (my ($source, $template_name) = each %opt::template) {
	    if(open(my $tmpl, "<", $source)) {
		local $/; # $/ = undef => slurp whole file
		my $content = <$tmpl>;
		push @Global::template_names, $template_name;
		push @Global::template_contents, $content;
		::debug("tmpl","Name: $template_name\n$content\n");
	    } else {
		::error("Cannot open '$source'.");
		wait_and_exit(255);
	    }
	}
    }
    if(not defined $opt::recstart and
       not defined $opt::recend) { $opt::recend = "\n"; }
    $Global::blocksize = multiply_binary_prefix($opt::blocksize || "1M");
    if($Global::blocksize > 2**31-1 and not $opt::pipepart) {
	warning("--blocksize >= 2G causes problems. Using 2G-1.");
	$Global::blocksize = 2**31-1;
    }
    if($^O eq "cygwin" and
       ($opt::pipe or $opt::pipepart or $opt::roundrobin)
       and $Global::blocksize > 65535) {
	warning("--blocksize >= 64K causes problems on Cygwin.");
    }
    $opt::memfree = multiply_binary_prefix($opt::memfree);
    $opt::memsuspend = multiply_binary_prefix($opt::memsuspend);
    $Global::memlimit = $opt::memsuspend + $opt::memfree;
    check_invalid_option_combinations();
    if((defined $opt::fifo or defined $opt::cat) and not $opt::pipepart) {
	$opt::pipe = 1;
    }
    if(defined $opt::minversion) {
	print $Global::version,"\n";
	if($Global::version < $opt::minversion) {
	    wait_and_exit(255);
	} else {
	    wait_and_exit(0);
	}
    }
    if(not defined $opt::delay) {
	# Set --delay to --sshdelay if not set
	$opt::delay = $opt::sshdelay;
    }
    $Global::sshdelayauto = $opt::sshdelay =~ s/auto$//;
    $opt::sshdelay = multiply_time_units($opt::sshdelay);
    $Global::delayauto = $opt::delay =~ s/auto$//;
    $opt::delay = multiply_time_units($opt::delay);
    if($opt::compress_program) {
	$opt::compress = 1;
	$opt::decompress_program ||= $opt::compress_program." -dc";
    }

    if(defined $opt::results) {
	# Is the output a dir or CSV-file?
	if($opt::results =~ /\.csv$/i) {
	    # CSV with , as separator
	    $Global::csvsep = ",";
	    $Global::membuffer ||= 1;
	} elsif($opt::results =~ /\.tsv$/i) {
	    # CSV with TAB as separator
	    $Global::csvsep = "\t";
	    $Global::membuffer ||= 1;
	} elsif($opt::results =~ /\.json$/i) {
	    # JSON output
	    $Global::jsonout ||= 1;
	    $Global::membuffer ||= 1;
	}
    }
    if($opt::compress) {
	my ($compress, $decompress) = find_compression_program();
	$opt::compress_program ||= $compress;
	$opt::decompress_program ||= $decompress;
	if(($opt::results and not $Global::csvsep) or $Global::files) {
	    # No need for decompressing
	    $opt::decompress_program = "cat >/dev/null";
	}
    }
    if(defined $opt::dryrun) {
	# Force grouping due to bug #51039: --dry-run --timeout 3600 -u breaks
	$opt::ungroup = 0;
	$opt::group = 1;
    }
    if(defined $opt::nonall) {
	# Append a dummy empty argument if there are no arguments
	# on the command line to avoid reading from STDIN.
	# arg_sep = random 50 char
	# \0noarg => nothing (not the empty string)
	$Global::arg_sep = join "",
	map { (0..9,"a".."z","A".."Z")[rand(62)] } (1..50);
	push @ARGV, $Global::arg_sep, "\0noarg";
    }
    if(defined $opt::tee) {
	if(not defined $opt::jobs) {
	    $opt::jobs = 0;
	}
    }
    if(defined $opt::tty) {
	# Defaults for --tty: -j1 -u
	# Can be overridden with -jXXX -g
	if(not defined $opt::jobs) {
	    $opt::jobs = 1;
	}
	if(not defined $opt::group) {
	    $opt::ungroup = 1;
	}
    }
    if(@opt::trc) {
	push @Global::ret_files, @opt::trc;
	if(not @Global::transfer_files) {
	    # Defaults to --transferfile {}
	    push @Global::transfer_files, $opt::i || $opt::I || "{}";
	}
	$opt::cleanup = 1;
    }
    if(defined $opt::max_lines) {
	if($opt::max_lines eq "-0") {
	    # -l -0 (swallowed -0)
	    $opt::max_lines = 1;
	    $opt::null = 1;
	    $/ = "\0";
	} else {
	    $opt::max_lines = multiply_binary_prefix($opt::max_lines);
	    if ($opt::max_lines == 0) {
		# If not given (or if 0 is given) => 1
		$opt::max_lines = 1;
	    }
	}

	$Global::max_lines = $opt::max_lines;
	if(not $opt::pipe) {
	    # --pipe -L means length of record - not max_number_of_args
	    $Global::max_number_of_args ||= $Global::max_lines;
	}
    }

    # Read more than one arg at a time (-L, -N)
    if(defined $opt::L) {
	$opt::L = multiply_binary_prefix($opt::L);
	$Global::max_lines = $opt::L;
	if(not $opt::pipe) {
	    # --pipe -L means length of record - not max_number_of_args
	    $Global::max_number_of_args ||= $Global::max_lines;
	}
    }
    if(defined $opt::max_replace_args) {
	$opt::max_replace_args =
	    multiply_binary_prefix($opt::max_replace_args);
	$Global::max_number_of_args = $opt::max_replace_args;
	$Global::ContextReplace = 1;
    }
    if((defined $opt::L or defined $opt::max_replace_args)
       and
       not ($opt::xargs or $opt::m)) {
	$Global::ContextReplace = 1;
    }
    if(grep /^$Global::arg_sep\+?$|^$Global::arg_file_sep\+?$/o, @ARGV) {
	# Deal with ::: :::+ :::: and ::::+
	@ARGV = read_args_from_command_line();
    }
    parse_semaphore();

    if(defined $opt::eta) { $opt::progress = $opt::eta; }
    if(defined $opt::bar) { $opt::progress = $opt::bar; }
    if(defined $opt::bar or defined $opt::latestline) {
	my $fh = $Global::status_fd || *STDERR;
	# Activate decode_utf8
	eval q{
	    # Enable utf8 if possible
	    use utf8;
	    binmode $fh, "encoding(utf8)";
	    *decode_utf8 = \&Encode::decode_utf8;
	};
	if(eval { decode_utf8("x") }) {
	    # Great: decode works
	} else {
	    # UTF8-decode not supported: Dummy decode
	    eval q{sub decode_utf8($;$) { $_[0]; }};
	}
	# Activate decode_utf8
	eval q{
	    # Enable utf8 if possible
	    use utf8;
	    use Encode             qw( encode_utf8 );
	    use Text::CharWidth    qw( mbswidth );
	    use Unicode::Normalize qw( NFC NFD );
	};
	if(eval { mbswidth("ヌー平行") }) {
	    # Great: mbswidth works
	} else {
	    # mbswidth not supported: Dummy mbswidth
	    eval q{ sub mbswidth { return length @_; } };
	}
    }

    # If you want GNU Parallel to be maintained in the future you
    # should keep this.
    # *YOU* will be harming free software by removing the notice.
    #
    # Funding a free software project is hard. GNU Parallel is no
    # exception. On top of that it seems the less visible a project
    # is, the harder it is to get funding. And the nature of GNU
    # Parallel is that it will never be seen by "the guy with the
    # checkbook", but only by the people doing the actual work.
    #
    # This problem has been covered by others - though no solution has
    # been found:
    # https://www.slideshare.net/NadiaEghbal/consider-the-maintainer
    # https://www.numfocus.org/blog/why-is-numpy-only-now-getting-funded/
    #
    # The FAQ tells you why the citation notice exists:
    # https://git.savannah.gnu.org/cgit/parallel.git/tree/doc/citation-notice-faq.txt
    #
    # If you want GNU Parallel to be maintained in the future, and not
    # just wither away like so many other free software tools, you
    # need to help finance the development.
    #
    # The citation notice is a simple way of doing so, as citations
    # makes it possible to me to get a job where I can maintain GNU
    # Parallel as part of the job.
    #
    # This means you can help financing development
    #
    #	WITHOUT PAYING A SINGLE CENT!
    #
    # Before implementing the citation notice it was discussed with
    # the users:
    # https://lists.gnu.org/archive/html/parallel/2013-11/msg00006.html
    #
    # Having to spend 10 seconds on running 'parallel --citation' once
    # is no doubt not an ideal solution, but no one has so far come up
    # with an ideal solution - neither for funding GNU Parallel nor
    # other free software.
    #
    # If you believe you have the perfect solution, you should try it
    # out, and if it works, you should post it on the email
    # list. Ideas that will cost work and which have not been tested
    # are, however, unlikely to be prioritized.
    #
    # Please note that GPL version 3 gives you the right to fork GNU
    # Parallel under a new name, but it does not give you the right to
    # distribute modified copies with the citation notice disabled in
    # a way where the software can be confused with GNU Parallel. To
    # do that you need to be the owner of the GNU Parallel
    # trademark. The xt:Commerce case shows this.
    #
    # Description of the xt:Commerce case in OLG Duesseldorf
    # https://web.archive.org/web/20180715073746/http://www.inta.org/INTABulletin/Pages/GERMANYGeneralPublicLicenseDoesNotPermitUseofThird-PartyTrademarksforAdvertisingModifiedVersionsofOpen-SourceSoftware.aspx
    #
    # The verdict in German
    # https://www.admody.com/urteilsdatenbank/cafe6fdaeed3/OLG-Duesseldorf_Urteil_vom_28-September-2010_Az_I-20-U-41-09
    # https://web.archive.org/web/20180715073717/https://www.admody.com/urteilsdatenbank/cafe6fdaeed3/OLG-Duesseldorf_Urteil_vom_28-September-2010_Az_I-20-U-41-09
    #
    # Other free software limiting derivates by the same name:
    # https://en.wikipedia.org/wiki/Red_Hat_Enterprise_Linux_derivatives#Legal_aspects
    # https://tm.joomla.org/trademark-faq.html
    # https://www.mozilla.org/en-US/foundation/trademarks/faq/
    #
    # Running 'parallel --citation' one single time takes less than 10
    # seconds, and will silence the citation notice for future
    # runs. If that is too much trouble for you, why not use one of
    # the alternatives instead?
    # See a list in: 'man parallel_alternatives'
    #
    # If you want GNU Parallel to be maintained in the future, you
    # should keep this line:
    citation_notice();
    # This is because _YOU_ actively make it harder to justify
    # spending time developing GNU Parallel by removing it.

    # If you disagree, please read (especially 77-):
    # https://www.fordfoundation.org/media/2976/roads-and-bridges-the-unseen-labor-behind-our-digital-infrastructure.pdf

    # *YOU* will be harming free software by removing the notice.  You
    # accept to be added to a public hall of shame by removing the
    # line.  That includes you, George and Andreas.

    parse_halt();

    if($ENV{'PARALLEL_ENV'}) {
	# Read environment and set $Global::parallel_env
	# Must be done before is_acceptable_command_line_length()
	my $penv = $ENV{'PARALLEL_ENV'};
	# unset $PARALLEL_ENV: It should not be given to children
	# because it takes up a lot of env space
	delete $ENV{'PARALLEL_ENV'};
	if(-e $penv) {
	    # This is a file/fifo: Replace envvar with content of file
	    open(my $parallel_env, "<", $penv) ||
		::die_bug("Cannot read parallel_env from $penv");
	    local $/; # Put <> in slurp mode
	    $penv = <$parallel_env>;
	    close $parallel_env;
	}
	# Map \001 to \n to make it easer to quote \n in $PARALLEL_ENV
	$penv =~ s/\001/\n/g;
	if($penv =~ /\0/) {
	    ::warning('\0 (NUL) in environment is not supported');
	}
	$Global::parallel_env = $penv;
    }

    parse_sshlogin();
    if(defined $opt::show_limits) { show_limits(); }

    if(remote_hosts() and
       (defined $opt::X or defined $opt::m or defined $opt::xargs)) {
	# As we do not know the max line length on the remote machine
	# long commands generated by xargs may fail
	# If $opt::max_replace_args is set, it is probably safe
	::warning("Using -X or -m with --sshlogin may fail.");
    }

    if(not defined $opt::jobs) { $opt::jobs = "100%"; }
    open_joblog();
    open_json_csv();
    if(defined $opt::sqlmaster or defined $opt::sqlworker) {
	$Global::sql = SQL->new($opt::sqlmaster || $opt::sqlworker);
    }
    if(defined $opt::sqlworker) { $Global::membuffer ||= 1; }
    # The sqlmaster groups the arguments, so the should just read one
    if(defined $opt::sqlworker and not defined $opt::sqlmaster) {
	$Global::max_number_of_args = 1;
    }
    if(defined $Global::color or defined $opt::colorfailed) {
	Job::init_color();
    }
}

sub check_invalid_option_combinations() {
    if(defined $opt::timeout and
       $opt::timeout !~ /^\d+(\.\d+)?%?$|^(\d+(\.\d+)?[dhms])+$/i) {
	::error("--timeout must be seconds or percentage.");
	wait_and_exit(255);
    }
    if(defined $opt::fifo and defined $opt::cat) {
	::error("--fifo cannot be combined with --cat.");
	::wait_and_exit(255);
    }
    if(defined $opt::retries and defined $opt::roundrobin) {
	::error("--retries cannot be combined with --roundrobin.");
	::wait_and_exit(255);
    }
    if(defined $opt::pipepart and
       (defined $opt::L or defined $opt::max_lines
	or defined $opt::max_replace_args)) {
	::error("--pipepart is incompatible with --max-replace-args, ".
		"--max-lines, and -L.");
	wait_and_exit(255);
    }
    if(defined $opt::group and defined $opt::ungroup) {
	::error("--group cannot be combined with --ungroup.");
	::wait_and_exit(255);
    }
    if(defined $opt::group and defined $opt::linebuffer) {
	::error("--group cannot be combined with --line-buffer.");
	::wait_and_exit(255);
    }
    if(defined $opt::ungroup and defined $opt::linebuffer) {
	::error("--ungroup cannot be combined with --line-buffer.");
	::wait_and_exit(255);
    }
    if(defined $opt::tollef and not defined $opt::gnu) {
       ::error("--tollef has been retired.",
	       "Remove --tollef or use --gnu to override --tollef.");
       ::wait_and_exit(255);
    }
    if(defined $opt::retired) {
	    ::error("-g has been retired. Use --group.",
		    "-B has been retired. Use --bf.",
		    "-T has been retired. Use --tty.",
		    "-U has been retired. Use --er.",
		    "-W has been retired. Use --wd.",
		    "-Y has been retired. Use --shebang.",
		    "-H has been retired. Use --halt.",
		    "--sql has been retired. Use --sqlmaster.",
		    "--ctrlc has been retired.",
		    "--noctrlc has been retired.");
	    ::wait_and_exit(255);
    }
    if(defined $opt::groupby) {
	if(not defined $opt::pipe and not defined $opt::pipepart) {
	    $opt::pipe = 1;
	}
	if(defined $opt::remove_rec_sep) {
	    ::error("--remove-rec-sep is not compatible with --groupby");
	    ::wait_and_exit(255);
	}
	if(defined $opt::recstart) {
	    ::error("--recstart is not compatible with --groupby");
	    ::wait_and_exit(255);
	}
	if($opt::recend ne "\n") {
	    ::error("--recend is not compatible with --groupby");
	    ::wait_and_exit(255);
	}
    }
    sub unsafe_warn {
	# use --_unsafe to only generate a warning
	if($opt::_unsafe) { ::warning(@_); } else { ::error(@_); exit(255); }
    }
    if(defined $opt::results) {
	if($opt::nonall or $opt::onall) {
	    unsafe_warn("--(n)onall + --results not supported (yet).");
	}
    }
    sub test_safe_chars {
	my $var = shift;
	if($ENV{$var} =~ m{^[-a-z0-9_+,.%:/= ]*$}i) {
	    # OK
	} else {
	    unsafe_warn("\$$var can only contain [-a-z0-9_+,.%:/= ].");
	}
    }
    if($ENV{'TMPDIR'} =~ /\n/) {
	if(defined $opt::files) {
	    ::warning("Use --files0 when \$TMPDIR contains newline.");
	} elsif($Global::cshell
		and
		(defined $opt::cat or defined $opt::fifo)) {
	    ::warning("--cat/--fifo fails under csh ".
		      "if \$TMPDIR contains newline.");
	}
    } elsif($ENV{'TMPDIR'} =~ /\257/) {
	unsafe_warn("\$TMPDIR with \\257 (\257) is not supported.");
    } else{
	test_safe_chars('TMPDIR');
    }
    map { test_safe_chars($_); } qw(PARALLEL_HOME XDG_CONFIG_DIRS
				    PARALLEL_REMOTE_TMPDIR XDG_CACHE_HOME);
}

sub init_globals() {
    # Defaults:
    $Global::version = 20230822;
    $Global::progname = 'parallel';
    $::name = "GNU Parallel";
    $Global::infinity = 2**31;
    $Global::debug = 0;
    $Global::verbose = 0;
    # Don't quote every part of the command line
    $Global::quoting = 0;
    # Quote replacement strings
    $Global::quote_replace = 1;
    $Global::total_completed = 0;
    $Global::cache_replacement_eval = 1;
    # Read only table with default --rpl values
    %Global::replace =
	(
	 '{}'	=> '',
	 '{#}'	=> '1 $_=$job->seq()',
	 '{%}'	=> '1 $_=$job->slot()',
	 '{/}'	=> 's:.*/::',
	 '{//}' =>
	 ('$Global::use{"File::Basename"} ||= eval "use File::Basename; 1;"; '.
	  '$_ = dirname($_);'),
	 '{/.}' => 's:.*/::; s:\.[^/.]*$::;',
	 '{.}'	=> 's:\.[^/.]*$::',
	);
    %Global::plus =
	(
	 # {} = {+/}/{/}
	 #    = {.}.{+.}     = {+/}/{/.}.{+.}
	 #    = {..}.{+..}   = {+/}/{/..}.{+..}
	 #    = {...}.{+...} = {+/}/{/...}.{+...}
	 '{+/}' => 's:/[^/]*$:: || s:.*$::',
	 # a.b => b; a => ''
	 '{+.}' => 's:.*\.:: || s:.*$::',
	 # a.b.c => b.c; a.b => ''; a => ''
	 '{+..}' => 's:.*\.([^/.]*\.[^/.]*)$:$1: || s:.*$::',
	 '{+...}' => 's:.*\.([^/.]*\.[^/.]*\.[^/.]*)$:$1: || s:.*$::',
	 '{..}' => 's:\.[^/.]*\.[^/.]*$::',
	 '{...}' => 's:\.[^/.]*\.[^/.]*\.[^/.]*$::',
	 '{/..}' => 's:.*/::; s:\.[^/.]*\.[^/.]*$::',
	 '{/...}' => 's:.*/::; s:\.[^/.]*\.[^/.]*\.[^/.]*$::',
	 # n choose k = Binomial coefficient
	 '{choose_k}' => ('for $t (2..$#arg)'.
			  '{ if($arg[$t-1] ge $arg[$t]) { skip() } }'),
	 # unique values: Skip job if any args are the same
	 '{uniq}' => 'if(::uniq(@arg) != @arg) { skip(); }',
	 # {##} = number of jobs
	 '{##}' => '1 $_=total_jobs()',
	 # {0%} = 0-padded jobslot
	 '{0%}' => ('1 $f=1+int((log($Global::max_jobs_running||1)/log(10)));'.
		    '$_=sprintf("%0${f}d",slot())'),
	 # {0%} = 0-padded seq
	 '{0#}' => ('1 $f=1+int((log(total_jobs())/log(10)));'.
		    '$_=sprintf("%0${f}d",seq())'),

	 ## Bash inspired replacement strings
	 # Bash ${a:-myval}
	 '{:-([^}]+?)}' => '$_ ||= $$1',
	 # Bash ${a:2}
	 '{:(\d+?)}' => 'substr($_,0,$$1) = ""',
	 # Bash ${a:2:3}
	 '{:(\d+?):(\d+?)}' => '$_ = substr($_,$$1,$$2);',
	 # echo {#z.*z.} ::: z.z.z.foo => z.foo
	 # echo {##z.*z.} ::: z.z.z.foo => foo
	 # Bash ${a#bc}
	 '{#([^#}][^}]*?)}' =>
	 '$nongreedy=::make_regexp_ungreedy($$1);s/^$nongreedy(.*)/$1/;',
	 # Bash ${a##bc}
	 '{##([^#}][^}]*?)}' => 's/^$$1//;',
	 # echo {%.z.*z} ::: foo.z.z.z => foo.z
	 # echo {%%.z.*z} ::: foo.z.z.z => foo
	 # Bash ${a%def}
	 '{%([^}]+?)}' =>
	 '$nongreedy=::make_regexp_ungreedy($$1);s/(.*)$nongreedy$/$1/;',
	 # Bash ${a%%def}
	 '{%%([^}]+?)}' => 's/$$1$//;',
	 # Bash ${a/def/ghi} ${a/def/}
	 '{/([^#%}/]+?)/([^}]*?)}' => 's/$$1/$$2/;',
	 # Bash ${a/#def/ghi} ${a/#def/}
	 '{/#([^}]+?)/([^}]*?)}' => 's/^$$1/$$2/g;',
	 # Bash ${a/%def/ghi} ${a/%def/}
	 '{/%([^}]+?)/([^}]*?)}' => 's/$$1$/$$2/g;',
	 # Bash ${a//def/ghi} ${a//def/}
	 '{//([^}]+?)/([^}]*?)}' => 's/$$1/$$2/g;',
	 # Bash ${a^a}
	 '{^([^}]+?)}' => 's/^($$1)/uc($1)/e;',
	 # Bash ${a^^a}
	 '{^^([^}]+?)}' => 's/($$1)/uc($1)/eg;',
	 # Bash ${a,A}
	 '{,([^}]+?)}' => 's/^($$1)/lc($1)/e;',
	 # Bash ${a,,A}
	 '{,,([^}]+?)}' => 's/($$1)/lc($1)/eg;',

	 # {slot} = $PARALLEL_JOBSLOT
	 '{slot}' => '1 $_="\${PARALLEL_JOBSLOT}";uq()',
	 # {host} = ssh host
	 '{host}' => '1 $_="\${PARALLEL_SSHHOST}";uq()',
	 # {sshlogin} = sshlogin
	 '{sshlogin}' => '1 $_="\${PARALLEL_SSHLOGIN}";uq()',
	 # {hgrp} = hostgroups of the host
	 '{hgrp}' => '1 $_="\${PARALLEL_HOSTGROUPS}";uq()',
	 # {agrp} = hostgroups of the argument
	 '{agrp}' => '1 $_="\${PARALLEL_ARGHOSTGROUPS}";uq()',
	);
    # Modifiable copy of %Global::replace
    %Global::rpl = %Global::replace;
    $/ = "\n";
    $Global::ignore_empty = 0;
    $Global::interactive = 0;
    $Global::stderr_verbose = 0;
    $Global::default_simultaneous_sshlogins = 9;
    $Global::exitstatus = 0;
    $Global::arg_sep = ":::";
    $Global::arg_file_sep = "::::";
    $Global::trim = 'n';
    $Global::max_jobs_running = 0;
    $Global::job_already_run = '';
    $ENV{'TMPDIR'} ||= "/tmp";
    $ENV{'PARALLEL_REMOTE_TMPDIR'} ||= "/tmp";
    # bug #55398: set $OLDPWD when using --wd
    $ENV{'OLDPWD'} = $ENV{'PWD'};
    if(not $ENV{HOME}) {
	# $ENV{HOME} is sometimes not set if called from PHP
	::warning("\$HOME not set. Using /tmp.");
	$ENV{HOME} = "/tmp";
    }
    # no warnings to allow for undefined $XDG_*
    no warnings 'uninitialized';
    # If $PARALLEL_HOME is set, but does not exist, try making it.
    if(defined $ENV{'PARALLEL_HOME'}) {
	eval { File::Path::mkpath($ENV{'PARALLEL_HOME'}); };
    }
    # $xdg_config_home is needed to make env_parallel.fish stop complaining
    my $xdg_config_home = $ENV{'XDG_CONFIG_HOME'};
    # Use the first config dir that exists from:
    #   $PARALLEL_HOME
    #   $XDG_CONFIG_HOME/parallel
    #	$(each XDG_CONFIG_DIRS)/parallel
    #   $HOME/.parallel
    #
    # Keep only dirs that exist
    @Global::config_dirs =
	(grep { -d $_ }
	 $ENV{'PARALLEL_HOME'},
	 (map { "$_/parallel" }
	  $xdg_config_home,
	  split /:/, $ENV{'XDG_CONFIG_DIRS'}),
	 $ENV{'HOME'} . "/.parallel");
    # Use first dir as config dir
    $Global::config_dir = $Global::config_dirs[0] ||
	$ENV{'HOME'} . "/.parallel";
    if($ENV{'PARALLEL_HOME'} =~ /./ and not -d $ENV{'PARALLEL_HOME'}) {
	::warning("\$PARALLEL_HOME ($ENV{'PARALLEL_HOME'}) does not exist.");
	::warning("Using $Global::config_dir");
    }
    # Use the first cache dir that exists from:
    #   $PARALLEL_HOME
    #   $XDG_CACHE_HOME/parallel
    # Keep only dirs that exist
    @Global::cache_dirs = (grep { -d $_ }
			   $ENV{'PARALLEL_HOME'},
			   $ENV{'XDG_CACHE_HOME'}."/parallel");
    $Global::cache_dir = $Global::cache_dirs[0] ||
	$ENV{'HOME'} . "/.parallel";
    Job::init_color();
}

sub parse_halt() {
    # $opt::halt flavours
    # Uses:
    #	$opt::halt
    #	$Global::halt_when
    #	$Global::halt_fail
    #	$Global::halt_success
    #	$Global::halt_pct
    #	$Global::halt_count
    if(defined $opt::halt) {
	my %halt_expansion = (
	    "0" => "never",
	    "1" => "soon,fail=1",
	    "2" => "now,fail=1",
	    "-1" => "soon,success=1",
	    "-2" => "now,success=1",
	);
	# Expand -2,-1,0,1,2 into long form
	$opt::halt = $halt_expansion{$opt::halt} || $opt::halt;
	# --halt 5% == --halt soon,fail=5%
	$opt::halt =~ s/^(\d+)%$/soon,fail=$1%/;
	# Split: soon,fail=5%
	my ($when,$fail_success,$pct_count) = split /[,=]/, $opt::halt;
	if(not grep { $when eq $_ } qw(never soon now)) {
	    ::error("--halt must have 'never', 'soon', or 'now'.");
	    ::wait_and_exit(255);
	}
	$Global::halt_when = $when;
	if($when ne "never") {
	    if($fail_success eq "fail") {
		$Global::halt_fail = 1;
	    } elsif($fail_success eq "success") {
		$Global::halt_success = 1;
	    } elsif($fail_success eq "done") {
		$Global::halt_done = 1;
	    } else {
		::error("--halt $when must be followed by ,success or ,fail.");
		::wait_and_exit(255);
	    }
	    if($pct_count =~ /^(\d+)%$/) {
		$Global::halt_pct = $1/100;
	    } elsif($pct_count =~ /^(\d+)$/) {
		$Global::halt_count = $1;
	    } else {
		::error("--halt $when,$fail_success ".
			"must be followed by ,number or ,percent%.");
		::wait_and_exit(255);
	    }
	}
    }
}

sub parse_replacement_string_options() {
    # Deal with --rpl
    # Uses:
    #	%Global::rpl
    #	$Global::parensleft
    #	$Global::parensright
    #	$opt::parens
    #	$Global::parensleft
    #	$Global::parensright
    #	$opt::plus
    #	%Global::plus
    #	$opt::I
    #	$opt::U
    #	$opt::i
    #	$opt::basenamereplace
    #	$opt::dirnamereplace
    #	$opt::seqreplace
    #	$opt::slotreplace
    #	$opt::basenameextensionreplace

    sub rpl($$) {
	# Modify %Global::rpl
	# Replace $old with $new
	my ($old,$new) =  @_;
	if($old ne $new) {
	    $Global::rpl{$new} = $Global::rpl{$old};
	    delete $Global::rpl{$old};
	}
    }
    my $parens = "{==}";
    if(defined $opt::parens) { $parens = $opt::parens; }
    my $parenslen = 0.5*length $parens;
    $Global::parensleft = substr($parens,0,$parenslen);
    $Global::parensright = substr($parens,$parenslen);
    if(defined $opt::plus) { %Global::rpl = (%Global::plus,%Global::rpl); }
    if(defined $opt::I) { rpl('{}',$opt::I); }
    if(defined $opt::i and $opt::i) { rpl('{}',$opt::i); }
    if(defined $opt::U) { rpl('{.}',$opt::U); }
    if(defined $opt::basenamereplace) { rpl('{/}',$opt::basenamereplace); }
    if(defined $opt::dirnamereplace) { rpl('{//}',$opt::dirnamereplace); }
    if(defined $opt::seqreplace) { rpl('{#}',$opt::seqreplace); }
    if(defined $opt::slotreplace) { rpl('{%}',$opt::slotreplace); }
    if(defined $opt::basenameextensionreplace) {
       rpl('{/.}',$opt::basenameextensionreplace);
    }
    for(@opt::rpl) {
	# Create $Global::rpl entries for --rpl options
	# E.g: "{..} s:\.[^.]+$:;s:\.[^.]+$:;"
	my ($shorthand,$long) = split/\s/,$_,2;
	$Global::rpl{$shorthand} = $long;
    }
}

sub parse_semaphore() {
    # Semaphore defaults
    # Must be done before computing number of processes and max_line_length
    # because when running as a semaphore GNU Parallel does not read args
    # Uses:
    #	$opt::semaphore
    #	$Global::semaphore
    #	$opt::semaphoretimeout
    #	$Semaphore::timeout
    #	$opt::semaphorename
    #	$Semaphore::name
    #	$opt::fg
    #	$Semaphore::fg
    #	$opt::wait
    #	$Semaphore::wait
    #	$opt::bg
    #	@opt::a
    #	@Global::unget_argv
    #	$Global::default_simultaneous_sshlogins
    #	$opt::jobs
    #	$Global::interactive
    $Global::semaphore ||= ($0 =~ m:(^|/)sem$:); # called as 'sem'
    if(defined $opt::semaphore) { $Global::semaphore = 1; }
    if(defined $opt::semaphoretimeout) { $Global::semaphore = 1; }
    if(defined $opt::semaphorename) { $Global::semaphore = 1; }
    if(defined $opt::fg and not $opt::tmux and not $opt::tmuxpane) {
	$Global::semaphore = 1;
    }
    if(defined $opt::bg) { $Global::semaphore = 1; }
    if(defined $opt::wait and not $opt::sqlmaster) {
	$Global::semaphore = 1; @ARGV = "true";
    }
    if($Global::semaphore) {
	if(@opt::a) {
	    # Assign the first -a to STDIN
	    open(STDIN,"<",shift @opt::a);
	    if(@opt::a) {
		# We currently have no way of dealing with more -a
		::error("A semaphore cannot take input from more files\n");
		::wait_and_exit(255);
	    }
	}
	@opt::a = ("/dev/null");
	# Append a dummy empty argument
	# \0 => nothing (not the empty string)
	push(@Global::unget_argv, [Arg->new("\0noarg")]);
	$Semaphore::timeout = int(multiply_time_units($opt::semaphoretimeout))
	    || 0;
	if(defined $opt::semaphorename) {
	    $Semaphore::name = $opt::semaphorename;
	} else {
	    local $/ = "\n";
	    $Semaphore::name = `tty`;
	    chomp $Semaphore::name;
	}
	$Semaphore::fg = $opt::fg;
	$Semaphore::wait = $opt::wait;
	$Global::default_simultaneous_sshlogins = 1;
	if(not defined $opt::jobs) {
	    $opt::jobs = 1;
	}
	if($Global::interactive and $opt::bg) {
	    ::error("Jobs running in the ".
		    "background cannot be interactive.");
	    ::wait_and_exit(255);
	}
    }
}

sub record_env() {
    # Record current %ENV-keys in $PARALLEL_HOME/ignored_vars
    # Returns: N/A
    my $ignore_filename = $Global::config_dir . "/ignored_vars";
    if(open(my $vars_fh, ">", $ignore_filename)) {
	print $vars_fh map { $_,"\n" } keys %ENV;
    } else {
	::error("Cannot write to $ignore_filename.");
	::wait_and_exit(255);
    }
}

sub open_joblog() {
    # Open joblog as specified by --joblog
    # Uses:
    #	$opt::resume
    #	$opt::resume_failed
    #	$opt::joblog
    #	$opt::results
    #	$Global::job_already_run
    #	%Global::fh
    my $append = 0;
    if(($opt::resume or $opt::resume_failed)
       and
       not ($opt::joblog or $opt::results)) {
	::error("--resume and --resume-failed require --joblog or --results.");
	::wait_and_exit(255);
    }
    if(defined $opt::joblog and $opt::joblog =~ s/^\+//) {
	# --joblog +filename = append to filename
	$append = 1;
    }
    if($opt::joblog
       and
       ($opt::sqlmaster
	or
	not $opt::sqlworker)) {
	# Do not log if --sqlworker
	if($opt::resume || $opt::resume_failed || $opt::retry_failed) {
	    if(open(my $joblog_fh, "<", $opt::joblog)) {
		# Enable utf8 if possible
		eval q{ binmode $joblog_fh, "encoding(utf8)"; };
		# Read the joblog
		# Override $/ with \n because -d might be set
		local $/ = "\n";
		# If there is a header: Open as append later
		$append = <$joblog_fh>;
		my $joblog_regexp;
		if($opt::retry_failed) {
		    # Make a regexp that matches commands with exit+signal=0
		    # 4 host 1360490623.067 3.445 1023 1222 0 0 command
		    $joblog_regexp='^(\d+)(?:\t[^\t]+){5}\t0\t0\t';
		    my @group;
		    while(<$joblog_fh>) {
			if(/$joblog_regexp/o) {
			    # This is 30% faster than set_job_already_run($1);
			    vec($Global::job_already_run,($1||0),1) = 1;
			    $Global::total_completed++;
			    $group[$1-1] = "true";
			} elsif(/(\d+)\s+\S+(\s+[-0-9.]+){6}\s+(.*)$/) {
			    # Grab out the command
			    $group[$1-1] = $3;
			} else {
			    chomp;
			    ::error("Format of '$opt::joblog' is wrong: $_");
			    ::wait_and_exit(255);
			}
		    }
		    if(@group) {
			my ($outfh,$name) = ::tmpfile(SUFFIX => ".arg");
			unlink($name);
			# Put args into argfile
			if(grep /\0/, @group) {
			    # force --null to deal with \n in commandlines
			    ::warning("Command lines contain newline. ".
				      "Forcing --null.");
			    $opt::null = 1;
			    $/ = "\0";
			}
			# Replace \0 with '\n' as used in print_joblog()
			print $outfh (map { s/\0/\n/g; $_,$/ }
				      map { $_ } @group);
			seek $outfh, 0, 0;
			exit_if_disk_full();
			# Set filehandle to -a
			@opt::a = ($outfh);
		    }
		    # Remove $command (so -a is run)
		    @ARGV = ();
		}
		if($opt::resume || $opt::resume_failed) {
		    if($opt::resume_failed) {
			# Make a regexp that matches commands with exit+signal=0
			# 4 host 1360490623.067 3.445 1023 1222 0 0 command
			$joblog_regexp='^(\d+)(?:\t[^\t]+){5}\t0\t0\t';
		    } else {
			# Just match the job number
			$joblog_regexp='^(\d+)';
		    }
		    while(<$joblog_fh>) {
			if(/$joblog_regexp/o) {
			    # This is 30% faster than set_job_already_run($1);
			    vec($Global::job_already_run,($1||0),1) = 1;
			    $Global::total_completed++;
			} elsif(not /\d+\s+[^\s]+\s+([-0-9.]+\s+){6}/) {
			    ::error("Format of '$opt::joblog' is wrong: $_");
			    ::wait_and_exit(255);
			}
		    }
		}
		close $joblog_fh;
	    }
	    # $opt::null may be set if the commands contain \n
	    if($opt::null) { $/ = "\0"; }
	}
	if($opt::dryrun) {
	    # Do not write to joblog in a dry-run
	    if(not open($Global::joblog, ">", "/dev/null")) {
		::error("Cannot write to --joblog $opt::joblog.");
		::wait_and_exit(255);
	    }
	} elsif($append) {
	    # Append to joblog
	    if(not open($Global::joblog, ">>", $opt::joblog)) {
		::error("Cannot append to --joblog $opt::joblog.");
		::wait_and_exit(255);
	    }
	} else {
	    if($opt::joblog eq "-") {
		# Use STDOUT as joblog
		$Global::joblog = $Global::fh{1};
	    } elsif(not open($Global::joblog, ">", $opt::joblog)) {
		# Overwrite the joblog
		::error("Cannot write to --joblog $opt::joblog.");
		::wait_and_exit(255);
	    }
	    print $Global::joblog
		join("\t", "Seq", "Host", "Starttime", "JobRuntime",
		     "Send", "Receive", "Exitval", "Signal", "Command"
		). "\n";
	}
    }
}

sub open_json_csv() {
    if($opt::results) {
	# Output as JSON/CSV/TSV
	if($opt::results eq "-.csv"
	   or
	   $opt::results eq "-.tsv"
	   or
	   $opt::results eq "-.json") {
	    # Output as JSON/CSV/TSV on stdout
	    open $Global::csv_fh, ">&", "STDOUT" or
		::die_bug("Can't dup STDOUT in csv: $!");
	    # Do not print any other output to STDOUT
	    # by forcing all other output to /dev/null
	    open my $fd, ">", "/dev/null" or
		::die_bug("Can't >/dev/null in csv: $!");
	    $Global::fh{1} = $fd;
	    $Global::fh{2} = $fd;
	} elsif($Global::csvsep or $Global::jsonout) {
	    if(not open($Global::csv_fh,">",$opt::results)) {
		::error("Cannot open results file `$opt::results': ".
			"$!.");
		wait_and_exit(255);
	    }
	}
    }
}

sub find_compression_program() {
    # Find a fast compression program
    # Returns:
    #	$compress_program = compress program with options
    #	$decompress_program = decompress program with options

    # Search for these. Sorted by speed on 128 core

    # seq 120000000|shuf > 1gb &
    # apt-get update
    # apt install make g++ htop
    # wget -O - pi.dk/3 | bash
    # apt install zstd clzip liblz4-tool lzop pigz pxz gzip plzip pbzip2 lzma xz-utils lzip bzip2 lbzip2 lrzip pixz
    # git clone https://github.com/facebook/zstd.git
    # (cd zstd/contrib/pzstd; make -j; cp pzstd /usr/local/bin)
    # echo 'lrzip -L $((-$1))'	>/usr/local/bin/lrz
    # chmod +x /usr/local/bin/lrz
    # wait
    # onethread="zstd clzip lz4 lzop gzip lzma xz bzip2"
    # multithread="pzstd pigz pxz plzip pbzip2 lzip lbzip2 lrz pixz"
    # parallel --shuf -j1  --joblog jl-m --arg-sep ,  parallel --compress-program \'{3}" "-{2}\' cat ::: 1gb '>'/dev/null , 1 2 3 ,  {1..3} , $multithread
    # parallel --shuf -j50% --delay 1  --joblog jl-s --arg-sep ,  parallel --compress-program \'{3}" "-{2}\' cat ::: 1gb '>'/dev/null , 1 2 3 ,	 {1..3} , $onethread
    # sort -nk4 jl-?

    # 1-core:
    # 2-cores: pzstd zstd lz4 lzop pigz gzip lbzip2 pbzip2 lrz bzip2 lzma pxz plzip xz lzip clzip
    # 4-cores:
    # 8-cores: pzstd lz4 zstd pigz lzop lbzip2 pbzip2 gzip lzip lrz plzip pxz bzip2 lzma xz clzip
    # 16-cores: pzstd lz4 pigz lzop lbzip2 pbzip2 plzip lzip lrz pxz gzip lzma xz bzip2
    # 32-cores: pzstd lbzip2 pbzip2 zstd pigz lz4 lzop plzip lzip lrz gzip pxz lzma bzip2 xz clzip
    # 64-cores: pzstd lbzip2 pbzip2 pigz zstd pixz lz4 plzip lzop lzip lrz gzip pxz lzma bzip2 xz clzip
    # 128-core: pzstd lbzip2 pbzip2 zstd pixz lz4 pigz lzop plzip lzip gzip lrz pxz bzip2 lzma xz clzip

    my @prg = qw(pzstd lbzip2 pbzip2 zstd pixz lz4 pigz lzop plzip lzip gzip
		 lrz pxz bzip2 lzma xz clzip);
    for my $p (@prg) {
	if(which($p)) {
	    return ("$p -c -1","$p -dc");
	}
    }
    # Fall back to cat
    return ("cat","cat");
}

sub read_options() {
    # Read options from command line, profile and $PARALLEL
    # Uses:
    #	$opt::shebang_wrap
    #	$opt::shebang
    #	@ARGV
    #	$opt::plain
    #	@opt::profile
    #	$ENV{'HOME'}
    #	$ENV{'PARALLEL'}
    # Returns:
    #	@ARGV_no_opt = @ARGV without --options

    # This must be done first as this may exec myself
    if(defined $ARGV[0] and ($ARGV[0] =~ /^--shebang/ or
			     $ARGV[0] =~ /^--shebang-?wrap/ or
			     $ARGV[0] =~ /^--hashbang/)) {
	# Program is called from #! line in script
	# remove --shebang-wrap if it is set
	$opt::shebang_wrap = ($ARGV[0] =~ s/^--shebang-?wrap *//);
	# remove --shebang if it is set
	$opt::shebang = ($ARGV[0] =~ s/^--shebang *//);
	# remove --hashbang if it is set
	$opt::shebang .= ($ARGV[0] =~ s/^--hashbang *//);
	if($opt::shebang) {
	    my $argfile = Q(pop @ARGV);
	    # exec myself to split $ARGV[0] into separate fields
	    exec "$0 --skip-first-line -a $argfile @ARGV";
	}
	if($opt::shebang_wrap) {
	    my @options;
	    my @parser;
	    if ($^O eq 'freebsd') {
		# FreeBSD's #! puts different values in @ARGV than Linux' does
		my @nooptions = @ARGV;
		get_options_from_array(\@nooptions);
		while($#ARGV > $#nooptions) {
		    push @options, shift @ARGV;
		}
		while(@ARGV and $ARGV[0] ne ":::") {
		    push @parser, shift @ARGV;
		}
		if(@ARGV and $ARGV[0] eq ":::") {
		    shift @ARGV;
		}
	    } else {
		@options = shift @ARGV;
	    }
	    my $script = Q(Q(shift @ARGV)); # TODO - test if script = " "
            my @args = map{ Q($_) } @ARGV;
	    # exec myself to split $ARGV[0] into separate fields
	    exec "$0 --_pipe-means-argfiles @options @parser $script ".
                "::: @args";
	}
    }
    if($ARGV[0] =~ / --shebang(-?wrap)? /) {
	::warning("--shebang and --shebang-wrap must be the first ".
		  "argument.\n");
    }

    Getopt::Long::Configure("bundling","require_order");
    my @ARGV_copy = @ARGV;
    my @ARGV_orig = @ARGV;
    # Check if there is a --profile to set @opt::profile
    get_options_from_array(\@ARGV_copy,"profile|J=s","plain") || die_usage();
    my @ARGV_profile = ();
    my @ARGV_env = ();
    if(not $opt::plain) {
	# Add options from $PARALLEL_HOME/config and other profiles
	my @config_profiles = (
	    "/etc/parallel/config",
	    (map { "$_/config" } @Global::config_dirs),
	    $ENV{'HOME'}."/.parallelrc");
	my @profiles = @config_profiles;
	if(@opt::profile) {
	    # --profile overrides default profiles
	    @profiles = ();
	    for my $profile (@opt::profile) {
		if($profile =~ m:^\./|^/:) {
		    # Look for ./profile in .
		    # Look for /profile in /
		    push @profiles, grep { -r $_ } $profile;
		} else {
		    # Look for the $profile in @Global::config_dirs
		    push @profiles, grep { -r $_ }
		    map { "$_/$profile" } @Global::config_dirs;
		}
	    }
	}
	for my $profile (@profiles) {
	    if(-r $profile) {
		::debug("init","Read $profile\n");
		local $/ = "\n";
		open (my $in_fh, "<", $profile) ||
		    ::die_bug("read-profile: $profile");
		while(<$in_fh>) {
		    /^\s*\#/ and next;
		    chomp;
		    push @ARGV_profile, shell_words($_);
		}
		close $in_fh;
	    } else {
		if(grep /^\Q$profile\E$/, @config_profiles) {
		    # config file is not required to exist
		} else {
		    ::error("$profile not readable.");
		    wait_and_exit(255);
		}
	    }
	}
	# Add options from shell variable $PARALLEL
	if($ENV{'PARALLEL'}) {
	    push @ARGV_env, shell_words($ENV{'PARALLEL'});
	}
	# Add options from env_parallel.csh via $PARALLEL_CSH
	if($ENV{'PARALLEL_CSH'}) {
	    push @ARGV_env, shell_words($ENV{'PARALLEL_CSH'});
	}
    }
    Getopt::Long::Configure("bundling","require_order");
    get_options_from_array(\@ARGV_profile) || die_usage();
    get_options_from_array(\@ARGV_env) || die_usage();
    get_options_from_array(\@ARGV) || die_usage();
    # What were the options given on the command line?
    # Used to start --sqlworker
    my $ai = arrayindex(\@ARGV_orig, \@ARGV);
    @Global::options_in_argv = @ARGV_orig[0..$ai-1];
    # Prepend non-options to @ARGV (such as commands like 'nice')
    unshift @ARGV, @ARGV_profile, @ARGV_env;
    return @ARGV;
}

sub arrayindex() {
    # Similar to Perl's index function, but for arrays
    # Input:
    #	$arr_ref1 = ref to @array1 to search in
    #	$arr_ref2 = ref to @array2 to search for
    # Returns:
    #	$pos = position of @array1 in @array2, -1 if not found
    my ($arr_ref1,$arr_ref2) = @_;
    my $array1_as_string = join "", map { "\0".$_ } @$arr_ref1;
    my $array2_as_string = join "", map { "\0".$_ } @$arr_ref2;
    my $i = index($array1_as_string,$array2_as_string,0);
    if($i == -1) { return -1 }
    my @before = split /\0/, substr($array1_as_string,0,$i);
    return $#before;
}

sub read_args_from_command_line() {
    # Arguments given on the command line after:
    #	::: ($Global::arg_sep)
    #	:::: ($Global::arg_file_sep)
    #	:::+ ($Global::arg_sep with --link)
    #	::::+ ($Global::arg_file_sep with --link)
    # Removes the arguments from @ARGV and:
    # - puts filenames into -a
    # - puts arguments into files and add the files to -a
    # - adds --linkinputsource with 0/1 for each -a depending on :::+/::::+
    # Input:
    #	@::ARGV = command option ::: arg arg arg :::: argfiles
    # Uses:
    #	$Global::arg_sep
    #	$Global::arg_file_sep
    #	$opt::_pipe_means_argfiles
    #	$opt::pipe
    #	@opt::a
    # Returns:
    #	@argv_no_argsep = @::ARGV without ::: and :::: and following args
    my @new_argv = ();
    for(my $arg = shift @ARGV; @ARGV; $arg = shift @ARGV) {
	if($arg eq $Global::arg_sep
	   or
	   $arg eq $Global::arg_sep."+"
	   or
	   $arg eq $Global::arg_file_sep
	   or
	   $arg eq $Global::arg_file_sep."+") {
	    my $group_sep = $arg; # This group of args is args or argfiles
	    my @group;
	    while(defined ($arg = shift @ARGV)) {
		if($arg eq $Global::arg_sep
		   or
		   $arg eq $Global::arg_sep."+"
		   or
		   $arg eq $Global::arg_file_sep
		   or
		   $arg eq $Global::arg_file_sep."+") {
		    # exit while loop if finding new separator
		    last;
		} else {
		    # If not hitting ::: :::+ :::: or ::::+
		    # Append it to the group
		    push @group, $arg;
		}
	    }
	    my $is_linked = ($group_sep =~ /\+$/) ? 1 : 0;
	    my $is_file = ($group_sep eq $Global::arg_file_sep
			   or
			   $group_sep eq $Global::arg_file_sep."+");
	    if($is_file) {
		# :::: / ::::+
		push @opt::linkinputsource, map { $is_linked } @group;
	    } else {
		# ::: / :::+
		push @opt::linkinputsource, $is_linked;
	    }
	    if($is_file
	       or ($opt::_pipe_means_argfiles and $opt::pipe)
		) {
		# Group of file names on the command line.
		# Append args into -a
		push @opt::a, @group;
	    } else {
		# Group of arguments on the command line.
		# Put them into a file.
		# Create argfile
		my ($outfh,$name) = ::tmpfile(SUFFIX => ".arg");
		unlink($name);
		# Put args into argfile
		print $outfh map { $_,$/ } @group;
		seek $outfh, 0, 0;
		exit_if_disk_full();
		# Append filehandle to -a
		push @opt::a, $outfh;
	    }
	    if(defined($arg)) {
		# $arg is ::: :::+ :::: or ::::+
		# so there is another group
		redo;
	    } else {
		# $arg is undef -> @ARGV empty
		last;
	    }
	}
	push @new_argv, $arg;
    }
    # Output: @ARGV = command to run with options
    return @new_argv;
}

sub cleanup() {
    # Returns: N/A
    unlink keys %Global::unlink;
    map { rmdir $_ } keys %Global::unlink;
    if(@opt::basefile and $opt::cleanup) { cleanup_basefile(); }
    for(keys %Global::sshmaster) {
	# If 'ssh -M's are running: kill them
	kill "TERM", $_;
    }
}


sub __QUOTING_ARGUMENTS_FOR_SHELL__() {}

sub shell_quote(@) {
    # Input:
    #	@strings = strings to be quoted
    # Returns:
    #	@shell_quoted_strings = string quoted as needed by the shell
    return wantarray ? (map { Q($_) } @_) : (join" ",map { Q($_) } @_);
}

sub shell_quote_scalar_rc($) {
    # Quote for the rc-shell
    my $a = $_[0];
    if(defined $a) {
	if(($a =~ s/'/''/g)
	   +
	   ($a =~ s/[\n\002-\011\013-\032\\\#\?\`\(\)\{\}\[\]\^\*\<\=\>\~\|\; \"\!\$\&\'\202-\377]+/'$&'/go)) {
	    # A string was replaced
	    # No need to test for "" or \0
	} elsif($a eq "") {
	    $a = "''";
	} elsif($a eq "\0") {
	    $a = "";
	}
    }
    return $a;
}

sub shell_quote_scalar_csh($) {
    # Quote for (t)csh
    my $a = $_[0];
    if(defined $a) {
	# $a =~ s/([\002-\011\013-\032\\\#\?\`\(\)\{\}\[\]\^\*\>\<\~\|\; \"\!\$\&\'\202-\377])/\\$1/g;
	# This is 1% faster than the above
	if(($a =~ s/[\002-\011\013-\032\\\#\?\`\(\)\{\}\[\]\^\*\<\=\>\~\|\; \"\!\$\&\'\202-\377]/\\$&/go)
	   +
	   # quote newline in csh as \\\n
	   ($a =~ s/[\n]/"\\\n"/go)) {
	    # A string was replaced
	    # No need to test for "" or \0
	} elsif($a eq "") {
	    $a = "''";
	} elsif($a eq "\0") {
	    $a = "";
	}
    }
    return $a;
}

sub shell_quote_scalar_default($) {
    # Quote for other shells (Bourne compatibles)
    # Inputs:
    #	$string = string to be quoted
    # Returns:
    #	$shell_quoted = string quoted as needed by the shell
    local $_ = $_[0];
    if(/[^-_.+a-z0-9\/]/i) {
	s/'+/'"$&"'/g;	# "-quote '-quotes: ''' => "'''"
	$_ = "'$_'";	# '-quote entire string
	s/^''//;	# Remove unneeded '' at ends
	s/''$//;	# (faster than s/^''|''$//g)
	return $_;
    } elsif ($_ eq "") {
	return "''";
    } else {
	# No quoting needed
	return $_;
    }
}

sub shell_quote_scalar($) {
    # Quote the string so the shell will not expand any special chars
    # Inputs:
    #	$string = string to be quoted
    # Returns:
    #	$shell_quoted = string quoted as needed by the shell

    # Speed optimization: Choose the correct shell_quote_scalar_*
    # and call that directly from now on
    no warnings 'redefine';
    if($Global::cshell) {
	# (t)csh
	*shell_quote_scalar = \&shell_quote_scalar_csh;
    } elsif($Global::shell =~ m:(^|/)rc$:) {
	# rc-shell
	*shell_quote_scalar = \&shell_quote_scalar_rc;
    } else {
	# other shells
	*shell_quote_scalar = \&shell_quote_scalar_default;
    }
    # The sub is now redefined. Call it
    return shell_quote_scalar($_[0]);
}

sub Q($) {
    # Q alias for ::shell_quote_scalar
    my $ret = shell_quote_scalar($_[0]);
    no warnings 'redefine';
    *Q = \&::shell_quote_scalar;
    return $ret;
}

sub shell_quote_file($) {
    # Quote the string so shell will not expand any special chars
    # and prepend ./ if needed
    # Input:
    #	$filename = filename to be shell quoted
    # Returns:
    #	$quoted_filename = filename quoted with \ and ./ if needed
    my $a = shift;
    if(defined $a) {
	if($a =~ m:^/: or $a =~ m:^\./:) {
	    # /abs/path or ./rel/path => skip
	} else {
	    # rel/path => ./rel/path
	    $a = "./".$a;
	}
    }
    return Q($a);
}

sub shell_words(@) {
    # Input:
    #	$string = shell line
    # Returns:
    #	@shell_words = $string split into words as shell would do
    $Global::use{"Text::ParseWords"} ||= eval "use Text::ParseWords; 1;";
    return Text::ParseWords::shellwords(@_);
}

sub perl_quote_scalar($) {
    # Quote the string so perl's eval will not expand any special chars
    # Inputs:
    #	$string = string to be quoted
    # Returns:
    #	$perl_quoted = string quoted with \ as needed by perl's eval
    my $a = $_[0];
    if(defined $a) {
	$a =~ s/[\\\"\$\@]/\\$&/go;
    }
    return $a;
}

# -w complains about prototype
sub pQ($) {
    # pQ alias for ::perl_quote_scalar
    my $ret = perl_quote_scalar($_[0]);
    *pQ = \&::perl_quote_scalar;
    return $ret;
}

sub unquote_printf() {
    # Convert \t \n \r \000 \0
    # Inputs:
    #	$string = string with \t \n \r \num \0
    # Returns:
    #	$replaced = string with TAB NEWLINE CR <ascii-num> NUL
    $_ = shift;
    s/\\t/\t/g;
    s/\\n/\n/g;
    s/\\r/\r/g;
    s/\\(\d\d\d)/eval 'sprintf "\\'.$1.'"'/ge;
    s/\\(\d)/eval 'sprintf "\\'.$1.'"'/ge;
    return $_;
}


sub __FILEHANDLES__() {}


sub save_stdin_stdout_stderr() {
    # Remember the original STDIN, STDOUT and STDERR
    # and file descriptors opened by the shell (e.g. 3>/tmp/foo)
    # Uses:
    #	%Global::fh
    #	$Global::original_stderr
    #	$Global::original_stdin
    # Returns: N/A

    # TODO Disabled until we have an open3 that will take n filehandles
    # for my $fdno (1..61) {
    # # /dev/fd/62 and above are used by bash for <(cmd)
    # # Find file descriptors that are already opened (by the shell)
    # Only focus on stdout+stderr for now
    for my $fdno (1..2) {
	my $fh;
	# 2-argument-open is used to be compatible with old perl 5.8.0
	# bug #43570: Perl 5.8.0 creates 61 files
	if(open($fh,">&=$fdno")) {
	    $Global::fh{$fdno}=$fh;
	}
    }
    open $Global::original_stderr, ">&", "STDERR" or
	::die_bug("Can't dup STDERR: $!");
    open $Global::status_fd, ">&", "STDERR" or
	::die_bug("Can't dup STDERR: $!");
    open $Global::original_stdin, "<&", "STDIN" or
	::die_bug("Can't dup STDIN: $!");
}

sub enough_file_handles() {
    # Check that we have enough filehandles available for starting
    # another job
    # Uses:
    #	$opt::ungroup
    #	%Global::fh
    # Returns:
    #	1 if ungrouped (thus not needing extra filehandles)
    #	0 if too few filehandles
    #	1 if enough filehandles
    if(not $opt::ungroup) {
	my %fh;
	my $enough_filehandles = 1;
	# perl uses 7 filehandles for something?
	# open3 uses 2 extra filehandles temporarily
	# We need a filehandle for each redirected file descriptor
	# (normally just STDOUT and STDERR)
	for my $i (1..(7+2+keys %Global::fh)) {
	    $enough_filehandles &&= open($fh{$i}, "<", "/dev/null");
	}
	for (values %fh) { close $_; }
	return $enough_filehandles;
    } else {
	# Ungrouped does not need extra file handles
	return 1;
    }
}

sub open_or_exit($) {
    # Open a file name or exit if the file cannot be opened
    # Inputs:
    #	$file = filehandle or filename to open
    # Uses:
    #	$Global::original_stdin
    # Returns:
    #	$fh = file handle to read-opened file
    my $file = shift;
    if($file eq "-") {
	return ($Global::original_stdin || *STDIN);
    }
    if(ref $file eq "GLOB") {
	# This is an open filehandle
	return $file;
    }
    my $fh = gensym;
    if(not open($fh, "<", $file)) {
	::error("Cannot open input file `$file': No such file or directory.");
	wait_and_exit(255);
    }
    return $fh;
}

sub set_fh_blocking($) {
    # Set filehandle as blocking
    # Inputs:
    #	$fh = filehandle to be blocking
    # Returns:
    #	N/A
    my $fh = shift;
    $Global::use{"Fcntl"} ||= eval "use Fcntl qw(:DEFAULT :flock); 1;";
    my $flags;
    # Get the current flags on the filehandle
    fcntl($fh, &F_GETFL, $flags) || die $!;
    # Remove non-blocking from the flags
    $flags &= ~&O_NONBLOCK;
    # Set the flags on the filehandle
    fcntl($fh, &F_SETFL, $flags) || die $!;
}

sub set_fh_non_blocking($) {
    # Set filehandle as non-blocking
    # Inputs:
    #	$fh = filehandle to be blocking
    # Returns:
    #	N/A
    my $fh = shift;
    $Global::use{"Fcntl"} ||= eval "use Fcntl qw(:DEFAULT :flock); 1;";
    my $flags;
    # Get the current flags on the filehandle
    fcntl($fh, &F_GETFL, $flags) || die $!;
    # Add non-blocking to the flags
    $flags |= &O_NONBLOCK;
    # Set the flags on the filehandle
    fcntl($fh, &F_SETFL, $flags) || die $!;
}


sub __RUNNING_THE_JOBS_AND_PRINTING_PROGRESS__() {}


# Variable structure:
#
#    $Global::running{$pid} = Pointer to Job-object
#    @Global::virgin_jobs = Pointer to Job-object that have received no input
#    $Global::host{$sshlogin} = Pointer to SSHLogin-object
#    $Global::total_running = total number of running jobs
#    $Global::total_started = total jobs started
#    $Global::max_procs_file = filename if --jobs is given a filename
#    $Global::JobQueue = JobQueue object for the queue of jobs
#    $Global::timeoutq = queue of times where jobs timeout
#    $Global::newest_job = Job object of the most recent job started
#    $Global::newest_starttime = timestamp of $Global::newest_job
#    @Global::sshlogin
#    $Global::minimal_command_line_length = min len supported by all sshlogins
#    $Global::start_no_new_jobs = should more jobs be started?
#    $Global::original_stderr = file handle for STDERR when the program started
#    $Global::total_started = total number of jobs started
#    $Global::joblog = filehandle of joblog
#    $Global::debug = Is debugging on?
#    $Global::exitstatus = status code of GNU Parallel
#    $Global::quoting = quote the command to run

sub init_run_jobs() {
    # Set Global variables and progress signal handlers
    # Do the copying of basefiles
    # Returns: N/A
    $Global::total_running = 0;
    $Global::total_started = 0;
    $SIG{USR1} = \&list_running_jobs;
    $SIG{USR2} = \&toggle_progress;
    if(@opt::basefile) { setup_basefile(); }
}

{
    my $last_time;
    my %last_mtime;
    my $max_procs_file_last_mod;

    sub changed_procs_file {
	# If --jobs is a file and it is modfied:
	# Force recomputing of max_jobs_running for each $sshlogin
	# Uses:
	#   $Global::max_procs_file
	#   %Global::host
	# Returns: N/A
	if($Global::max_procs_file) {
	    # --jobs filename
	    my $mtime = (stat($Global::max_procs_file))[9];
	    $max_procs_file_last_mod ||= 0;
	    if($mtime > $max_procs_file_last_mod) {
		# file changed: Force re-computing max_jobs_running
		$max_procs_file_last_mod = $mtime;
		for my $sshlogin (values %Global::host) {
		    $sshlogin->set_max_jobs_running(undef);
		}
	    }
	}
    }

    sub changed_sshloginfile {
	# If --slf is changed:
	#   reload --slf
	#   filter_hosts
	#   setup_basefile
	# Uses:
	#   @opt::sshloginfile
	#   @Global::sshlogin
	#   %Global::host
	#   $opt::filter_hosts
	# Returns: N/A
	if(@opt::sshloginfile) {
	    # Is --sshloginfile changed?
	    for my $slf (@opt::sshloginfile) {
		my $actual_file = expand_slf_shorthand($slf);
		my $mtime = (stat($actual_file))[9];
		$last_mtime{$actual_file} ||= $mtime;
		if($mtime - $last_mtime{$actual_file} > 1) {
		    ::debug("run",
			    "--sshloginfile $actual_file changed. reload\n");
		    $last_mtime{$actual_file} = $mtime;
		    # Reload $slf
		    # Empty sshlogins
		    @Global::sshlogin = ();
		    for (values %Global::host) {
			# Don't start new jobs on any host
			# except the ones added back later
			$_->set_max_jobs_running(0);
		    }
		    # This will set max_jobs_running on the SSHlogins
		    read_sshloginfile($actual_file);
		    parse_sshlogin();
		    $opt::filter_hosts and filter_hosts();
		    setup_basefile();
		}
	    }
	}
    }

    sub start_more_jobs {
	# Run start_another_job() but only if:
	#   * not $Global::start_no_new_jobs set
	#   * not JobQueue is empty
	#   * not load on server is too high
	#   * not server swapping
	#   * not too short time since last remote login
	# Uses:
	#   %Global::host
	#   $Global::start_no_new_jobs
	#   $Global::JobQueue
	#   $opt::pipe
	#   $opt::load
	#   $opt::noswap
	#   $opt::delay
	#   $Global::newest_starttime
	# Returns:
	#   $jobs_started = number of jobs started
	my $jobs_started = 0;
	if($Global::start_no_new_jobs) {
	    return $jobs_started;
	}
	if(time - ($last_time||0) > 1) {
	    # At most do this every second
	    $last_time = time;
	    changed_procs_file();
	    changed_sshloginfile();
	}
	# This will start 1 job on each --sshlogin (if possible)
	# thus distribute the jobs on the --sshlogins round robin
	for my $sshlogin (values %Global::host) {
	    if($Global::JobQueue->empty() and not $opt::pipe) {
		# No more jobs in the queue
		last;
	    }
	    debug("run", "Running jobs before on ", $sshlogin->string(), ": ",
		  $sshlogin->jobs_running(), "\n");
	    if ($sshlogin->jobs_running() < $sshlogin->max_jobs_running()) {
		if($opt::delay
		   and
		   $opt::delay-0.008 > ::now()-$Global::newest_starttime) {
		    # It has been too short since last start
		    next;
		}
		if($opt::load and $sshlogin->loadavg_too_high()) {
		    # The load is too high or unknown
		    next;
		}
		if($opt::noswap and $sshlogin->swapping()) {
		    # The server is swapping
		    next;
		}
		if($opt::limit and $sshlogin->limit()) {
		    # Over limit
		    next;
		}
		if(($opt::memfree or $opt::memsuspend)
		   and
		   $sshlogin->memfree() < $Global::memlimit) {
		    # The server has not enough mem free
		    ::debug("mem", "Not starting job: not enough mem\n");
		    next;
		}
		if($sshlogin->too_fast_remote_login()) {
		    # It has been too short since last login
		    next;
		}
		debug("run", $sshlogin->string(),
		      " has ", $sshlogin->jobs_running(),
		      " out of ", $sshlogin->max_jobs_running(),
		      " jobs running. Start another.\n");
		if(start_another_job($sshlogin) == 0) {
		    # No more jobs to start on this $sshlogin
		    debug("run","No jobs started on ",
			  $sshlogin->string(), "\n");
		    next;
		}
		$sshlogin->inc_jobs_running();
		$sshlogin->set_last_login_at(::now());
		$jobs_started++;
	    }
	    debug("run","Running jobs after on ", $sshlogin->string(), ": ",
		  $sshlogin->jobs_running(), " of ",
		  $sshlogin->max_jobs_running(), "\n");
	}

	return $jobs_started;
    }
}

{
    my $no_more_file_handles_warned;

    sub start_another_job() {
	# If there are enough filehandles
	#   and JobQueue not empty
	#   and not $job is in joblog
	# Then grab a job from Global::JobQueue,
	#   start it at sshlogin
	#   mark it as virgin_job
	# Inputs:
	#   $sshlogin = the SSHLogin to start the job on
	# Uses:
	#   $Global::JobQueue
	#   $opt::pipe
	#   $opt::results
	#   $opt::resume
	#   @Global::virgin_jobs
	# Returns:
	#   1 if another jobs was started
	#   0 otherwise
	my $sshlogin = shift;
	# Do we have enough file handles to start another job?
	if(enough_file_handles()) {
	    if($Global::JobQueue->empty() and not $opt::pipe) {
		# No more commands to run
		debug("start", "Not starting: JobQueue empty\n");
		return 0;
	    } else {
		my $job;
		# Skip jobs already in job log
		# Skip jobs already in results
		do {
		    $job = get_job_with_sshlogin($sshlogin);
		    if(not defined $job) {
			# No command available for that sshlogin
			debug("start", "Not starting: no jobs available for ",
			      $sshlogin->string(), "\n");
			return 0;
		    }
		    if($job->is_already_in_joblog()) {
			$job->free_slot();
		    }
		} while ($job->is_already_in_joblog()
			 or
			 ($opt::results and $opt::resume
			  and $job->is_already_in_results()));
		debug("start", "Command to run on '",
		      $job->sshlogin()->string(), "': '",
		      $job->replaced(),"'\n");
		if($job->start()) {
		    if($opt::pipe) {
			if($job->virgin()) {
			    push(@Global::virgin_jobs,$job);
			} else {
			    # Block already set: This is a retry
			    $job->write_block();
			}
		    }
		    debug("start", "Started as seq ", $job->seq(),
			  " pid:", $job->pid(), "\n");
		    return 1;
		} else {
		    # Not enough processes to run the job.
		    # Put it back on the queue.
		    $Global::JobQueue->unget($job);
		    # Count down the number of jobs to run for this SSHLogin.
		    my $max = $sshlogin->max_jobs_running();
		    if($max > 1) { $max--; } else {
			my @arg;
			for my $record (@{$job->{'commandline'}{'arg_list'}}) {
			    push @arg, map { $_->orig() } @$record;
			}
			::error("No more processes: cannot run a single job. ".
				"Something is wrong at @arg.");
			::wait_and_exit(255);
		    }
		    $sshlogin->set_max_jobs_running($max);
		    # Sleep up to 300 ms to give other processes time to die
		    ::usleep(rand()*300);
		    ::warning("No more processes: ".
			      "Decreasing number of running jobs to $max.",
			      "Try increasing 'ulimit -u' (try: ulimit -u `ulimit -Hu`)",
			      "or increasing 'nproc' in /etc/security/limits.conf",
			      "or increasing /proc/sys/kernel/pid_max");
		    return 0;
		}
	    }
	} else {
	    # No more file handles
	    $no_more_file_handles_warned++ or
		::warning("No more file handles. ",
			  "Try running 'parallel -j0 -N 100 --pipe parallel -j0'",
			  "or increasing 'ulimit -n' (try: ulimit -n `ulimit -Hn`)",
			  "or increasing 'nofile' in /etc/security/limits.conf",
			  "or increasing /proc/sys/fs/file-max");
	    debug("start", "No more file handles. ");
	    return 0;
	}
    }
}

sub init_progress() {
    # Uses:
    #	$opt::bar
    # Returns:
    #	list of computers for progress output
    $|=1;
    if($opt::bar) {
	return("","");
    }
    my %progress = progress();
    return ("\nComputers / CPU cores / Max jobs to run\n",
	    $progress{'workerlist'});
}

sub drain_job_queue(@) {
    # Uses:
    #	$opt::progress
    #	$Global::total_running
    #	$Global::max_jobs_running
    #	%Global::running
    #	$Global::JobQueue
    #	%Global::host
    #	$Global::start_no_new_jobs
    # Returns: N/A
    my @command = @_;
    if($opt::progress) {
	::status_no_nl(init_progress());
    }
    my $last_header = "";
    my $sleep = 0.2;
    my $sleepsum = 0;
    do {
	while($Global::total_running > 0) {
	    debug("init",$Global::total_running, "==", scalar
		  keys %Global::running," slots: ", $Global::max_jobs_running);
	    if($opt::pipe) {
		# When using --pipe sometimes file handles are not
		# closed properly
		for my $job (values %Global::running) {
		    close $job->fh(0,"w");
		}
	    }
	    if($opt::progress) {
		my %progress = progress();
		if($last_header ne $progress{'header'}) {
		    ::status("", $progress{'header'});
		    $last_header = $progress{'header'};
		}
		::status_no_nl("\r",$progress{'status'});
	    }
	    if($Global::total_running < $Global::max_jobs_running
	       and not $Global::JobQueue->empty()) {
		# These jobs may not be started because of loadavg
		# or too little time between each ssh login.
		if(start_more_jobs() > 0) {
		    # Exponential back-on if jobs were started
		    $sleep = $sleep/2+0.001;
		}
	    }
	    # Exponential back-off sleeping
	    $sleep = ::reap_usleep($sleep);
	    $sleepsum += $sleep;
	    if($sleepsum >= 1000) {
		# At most do this every second
		$sleepsum = 0;
		changed_procs_file();
		changed_sshloginfile();
		start_more_jobs();
	    }
	}
	if(not $Global::JobQueue->empty()) {
	    # These jobs may not be started:
	    # * because there the --filter-hosts has removed all
	    if(not %Global::host) {
		::error("There are no hosts left to run on.");
		::wait_and_exit(255);
	    }
	    # * because of loadavg
	    # * because of too little time between each ssh login.
	    $sleep = ::reap_usleep($sleep);
	    start_more_jobs();
	    if($Global::max_jobs_running == 0) {
		::warning("There are no job slots available. Increase --jobs.");
	    }
	}
	while($opt::sqlmaster and not $Global::sql->finished()) {
	    # SQL master
	    $sleep = ::reap_usleep($sleep);
	    start_more_jobs();
	    if($Global::start_sqlworker) {
		# Start an SQL worker as we are now sure there is work to do
		$Global::start_sqlworker = 0;
		if(my $pid = fork()) {
		    $Global::unkilled_sqlworker = $pid;
		} else {
		    # Replace --sql/--sqlandworker with --sqlworker
		    my @ARGV = (map { s/^--sql(andworker)?$/--sqlworker/; $_ }
				@Global::options_in_argv);
		    # exec the --sqlworker
		    exec($0,@ARGV,@command);
		}
	    }
	}
    } while ($Global::total_running > 0
	     or
	     not $Global::start_no_new_jobs and not $Global::JobQueue->empty()
	     or
	     $opt::sqlmaster and not $Global::sql->finished());
    if($opt::progress) {
	my %progress = progress();
	::status("\r".$progress{'status'});
    }
}

sub toggle_progress() {
    # Turn on/off progress view
    # Uses:
    #	$opt::progress
    # Returns: N/A
    $opt::progress = not $opt::progress;
    if($opt::progress) {
	::status_no_nl(init_progress());
    }
}

sub progress() {
    # Uses:
    #	$opt::bar
    #	$opt::eta
    #	%Global::host
    #	$Global::total_started
    # Returns:
    #	$workerlist = list of workers
    #	$header = that will fit on the screen
    #	$status = message that will fit on the screen
    if($opt::bar) {
	return ("workerlist" => "", "header" => "", "status" => bar());
    }
    my $eta = "";
    my ($status,$header)=("","");
    if($opt::eta) {
	my($total, $completed, $left, $pctcomplete, $avgtime, $this_eta) =
	    compute_eta();
	$eta = sprintf("ETA: %ds Left: %d AVG: %.2fs  ",
		       $this_eta, $left, $avgtime);
    }
    my $termcols = terminal_columns();
    my @workers = sort keys %Global::host;
    my %sshlogin = map { $_ eq ":" ? ($_ => "local") : ($_ => $_) } @workers;
    my $workerno = 1;
    my %workerno = map { ($_=>$workerno++) } @workers;
    my $workerlist = "";
    for my $w (@workers) {
	$workerlist .=
	$workerno{$w}.":".$sshlogin{$w} ." / ".
	    ($Global::host{$w}->ncpus() || "-")." / ".
	    $Global::host{$w}->max_jobs_running()."\n";
    }
    $status = "c"x($termcols+1);
    # Select an output format that will fit on a single line
    if(length $status > $termcols) {
	# sshlogin1:XX/XX/XX%/XX.Xs s2:XX/XX/XX%/XX.Xs s3:XX/XX/XX%/XX.Xs
	$header = "Computer:jobs running/jobs completed/".
	    "%of started jobs/Average seconds to complete";
	$status = $eta .
	    join(" ",map
		 {
		     if($Global::total_started) {
			 my $completed =
			     ($Global::host{$_}->jobs_completed()||0);
			 my $running = $Global::host{$_}->jobs_running();
			 my $time = $completed ? (time-$^T)/($completed) : "0";
			 sprintf("%s:%d/%d/%d%%/%.1fs ",
				 $sshlogin{$_}, $running, $completed,
				 ($running+$completed)*100
				 / $Global::total_started, $time);
		     }
		 } @workers);
    }
    if(length $status > $termcols) {
	# 1:XX/XX/XX%/X.Xs 2:XX/XX/XX%/X.Xs 3:XX/XX/XX%/X.Xs 4:XX/XX/XX%/X.Xs
	$header = "Computer:jobs running/jobs completed/%of started jobs";
	$status = $eta .
	    join(" ",map
		 {
		     if($Global::total_started) {
			 my $completed =
			     ($Global::host{$_}->jobs_completed()||0);
			 my $running = $Global::host{$_}->jobs_running();
			 my $time = $completed ? (time-$^T)/($completed) : "0";
			 sprintf("%s:%d/%d/%d%%/%.1fs ",
				 $workerno{$_}, $running, $completed,
				 ($running+$completed)*100
				 / $Global::total_started, $time);
		     }
		 } @workers);
    }
    if(length $status > $termcols) {
	# sshlogin1:XX/XX/XX% sshlogin2:XX/XX/XX% sshlogin3:XX/XX/XX%
	$header = "Computer:jobs running/jobs completed/%of started jobs";
	$status = $eta .
	    join(" ",map
		 {
		     if($Global::total_started) {
			 sprintf("%s:%d/%d/%d%%",
				 $sshlogin{$_},
				 $Global::host{$_}->jobs_running(),
				 ($Global::host{$_}->jobs_completed()||0),
				 ($Global::host{$_}->jobs_running()+
				  ($Global::host{$_}->jobs_completed()||0))*100
				 / $Global::total_started)
		     }
		 }
		 @workers);
    }
    if(length $status > $termcols) {
	# 1:XX/XX/XX% 2:XX/XX/XX% 3:XX/XX/XX% 4:XX/XX/XX% 5:XX/XX/XX%
	$header = "Computer:jobs running/jobs completed/%of started jobs";
	$status = $eta .
	    join(" ",map
		 {
		     if($Global::total_started) {
			 sprintf("%s:%d/%d/%d%%",
				 $workerno{$_},
				 $Global::host{$_}->jobs_running(),
				 ($Global::host{$_}->jobs_completed()||0),
				 ($Global::host{$_}->jobs_running()+
				  ($Global::host{$_}->jobs_completed()||0))*100
				 / $Global::total_started)
		     }
		 }
		 @workers);
    }
    if(length $status > $termcols) {
	# sshlogin1:XX/XX/XX% sshlogin2:XX/XX/XX% sshlogin3:XX/XX
	$header = "Computer:jobs running/jobs completed";
	$status = $eta .
	    join(" ",
		 map { sprintf("%s:%d/%d",
			       $sshlogin{$_}, $Global::host{$_}->jobs_running(),
			       ($Global::host{$_}->jobs_completed()||0)) }
		 @workers);
    }
    if(length $status > $termcols) {
	# sshlogin1:XX/XX sshlogin2:XX/XX sshlogin3:XX/XX sshlogin4:XX/XX
	$header = "Computer:jobs running/jobs completed";
	$status = $eta .
	    join(" ",
		 map { sprintf("%s:%d/%d",
			       $sshlogin{$_}, $Global::host{$_}->jobs_running(),
			       ($Global::host{$_}->jobs_completed()||0)) }
		 @workers);
    }
    if(length $status > $termcols) {
	# 1:XX/XX 2:XX/XX 3:XX/XX 4:XX/XX 5:XX/XX 6:XX/XX
	$header = "Computer:jobs running/jobs completed";
	$status = $eta .
	    join(" ",
		 map { sprintf("%s:%d/%d", $workerno{$_},
			       $Global::host{$_}->jobs_running(),
			       ($Global::host{$_}->jobs_completed()||0)) }
		 @workers);
    }
    if(length $status > $termcols) {
	# sshlogin1:XX sshlogin2:XX sshlogin3:XX sshlogin4:XX sshlogin5:XX
	$header = "Computer:jobs completed";
	$status = $eta .
	    join(" ",
		 map { sprintf("%s:%d", $sshlogin{$_},
			       ($Global::host{$_}->jobs_completed()||0)) }
		 @workers);
    }
    if(length $status > $termcols) {
	# 1:XX 2:XX 3:XX 4:XX 5:XX 6:XX
	$header = "Computer:jobs completed";
	$status = $eta .
	    join(" ",
		 map { sprintf("%s:%d",
			       $workerno{$_},
			       ($Global::host{$_}->jobs_completed()||0)) }
		 @workers);
    }
    return ("workerlist" => $workerlist, "header" => $header,
	    "status" => $status);
}

{

    my ($first_completed, $smoothed_avg_time, $last_eta);

    sub compute_eta {
	# Calculate important numbers for ETA
	# Returns:
	#   $total = number of jobs in total
	#   $completed = number of jobs completed
	#   $left = number of jobs left
	#   $pctcomplete = percent of jobs completed
	#   $avgtime = averaged time
	#   $eta = smoothed eta
	my $completed = $Global::total_completed;
	# In rare cases with -X will $completed > total_jobs()
	my $total = ::max($Global::JobQueue->total_jobs(),$completed);
	my $left = $total - $completed;
	if(not $completed) {
	    return($total, $completed, $left, 0, 0, 0);
	}
	my $pctcomplete = ::min($completed / $total,100);
	$first_completed ||= time;
	my $timepassed = (time - $first_completed);
	my $avgtime = $timepassed / $completed;
	$smoothed_avg_time ||= $avgtime;
	# Smooth the eta so it does not jump wildly
	$smoothed_avg_time = (1 - $pctcomplete) * $smoothed_avg_time +
	    $pctcomplete * $avgtime;
	my $eta = int($left * $smoothed_avg_time);
	if($eta*0.90 < $last_eta and $last_eta < $eta) {
	    # Eta jumped less that 10% up: Keep the last eta instead
	    $eta = $last_eta;
	} else {
	    $last_eta = $eta;
	}
	return($total, $completed, $left, $pctcomplete, $avgtime, $eta);
    }
}

{
    my ($rev,$reset);

    sub bar() {
	# Return:
	#   $status = bar with eta, completed jobs, arg and pct
	$rev ||= "\033[7m";
	$reset ||= "\033[0m";
	my($total, $completed, $left, $pctcomplete, $avgtime, $eta) =
	    compute_eta();
	my $arg = $Global::newest_job ?
	    $Global::newest_job->{'commandline'}->
	    replace_placeholders(["\257<\257>"],0,0) : "";
	$arg = decode_utf8($arg);
	my $eta_dhms = ::seconds_to_time_units($eta);
	my $bar_text =
	    sprintf("%d%% %d:%d=%s %s",
		    $pctcomplete*100, $completed, $left, $eta_dhms, $arg);
	my $terminal_width = terminal_columns();
	my $s = sprintf("%-${terminal_width}s",
			substr($bar_text." "x$terminal_width,
			       0,$terminal_width));
	my $width = int($terminal_width * $pctcomplete);
	substr($s,$width,0) = $reset;
	my $zenity = sprintf("%-${terminal_width}s",
			     substr("#   $eta sec $arg",
				    0,$terminal_width));
	# Prefix with zenity header
	$s = "\r" . $zenity . "\r" . $pctcomplete*100 .
	    "\r" . $rev . $s . $reset;
	return $s;
    }
}

{
    my ($rows,$columns,$last_update_time);

    sub compute_terminal_size() {
	# && true is to force spawning a shell and not just exec'ing
	my @tput = qx{ tput lines cols </dev/tty 2>/dev/null && true };
	$rows = 0 + $tput[0];
	$columns = 0 + $tput[1];
	if(not ($rows && $columns)) {
	    # && true is to force spawning a shell and not just exec'ing
	    my $stty = qx{ stty -a </dev/tty 2>/dev/null && true };
	    # FreeBSD/OpenBSD/NetBSD/Dragonfly/MirOS
	    # MacOSX/IRIX/AIX/Tru64
	    $stty =~ /(\d+) columns/ and do { $columns = $1; };
	    $stty =~ /(\d+) rows/ and do { $rows = $1; };
	    # GNU/Linux/Solaris
	    $stty =~ /columns (\d+)/ and do { $columns = $1; };
	    $stty =~ /rows (\d+)/ and do { $rows = $1; };
	    # Solaris-x86/HPUX/SCOsysV/UnixWare/OpenIndiana
	    $stty =~ /columns = (\d+)/ and do { $columns = $1; };
	    $stty =~ /rows = (\d+)/ and do { $rows = $1; };
	    # QNX
	    $stty =~ /rows=(\d+),(\d+)/ and do { ($rows,$columns) = ($1,$2); };
	}
	if(not ($rows && $columns)) {
	    # && true is to force spawning a shell and not just exec'ing
	    my $resize = qx{ resize 2>/dev/null && true };
	    $resize =~ /COLUMNS=(\d+);/ and do { $columns ||= $1; };
	    $resize =~ /LINES=(\d+);/ and do { $rows ||= $1; };
	}
	$rows ||= 24;
	$columns ||= 80;
    }

    sub update_terminal_size() {
	# Only update once per second.
	if($last_update_time < time) {
	    $last_update_time = time;
	    compute_terminal_size();
	    # Set signal WINdow CHange to force recompute
	    $SIG{WINCH} = \&compute_terminal_size;
	}
    }

    sub terminal_rows() {
	# Get the number of rows of the terminal.
	# Returns:
	#   number of rows of the screen
	update_terminal_size();
	return $rows;
    }

    sub terminal_columns() {
	# Get the number of columns of the terminal.
	# Returns:
	#   number of columns of the screen
	update_terminal_size();
	return $columns;
    }
}

sub untabify($) {
    # Convert \t into spaces
    my @out;
    my ($src);
    # Deal with multi-byte characters
    for my $src (split("\t",$_[0])) {
	push @out, $src. " "x(8-mbswidth($src)%8);
    }
    return join "",@out;
}

# Prototype forwarding
sub get_job_with_sshlogin($);
sub get_job_with_sshlogin($) {
    # Input:
    #	$sshlogin = which host should the job be run on?
    # Uses:
    #	$opt::hostgroups
    #	$Global::JobQueue
    # Returns:
    #	$job = next job object for $sshlogin if any available
    my $sshlogin = shift;
    my $job;

    if ($opt::hostgroups) {
	my @other_hostgroup_jobs = ();

	while($job = $Global::JobQueue->get()) {
	    if($sshlogin->in_hostgroups($job->hostgroups())) {
		# Found a job to be run on a hostgroup of this
		# $sshlogin
		last;
	    } else {
		# This job was not in the hostgroups of $sshlogin
		push @other_hostgroup_jobs, $job;
	    }
	}
	$Global::JobQueue->unget(@other_hostgroup_jobs);
	if(not defined $job) {
	    # No more jobs
	    return undef;
	}
    } else {
	$job = $Global::JobQueue->get();
	if(not defined $job) {
	    # No more jobs
	    ::debug("start", "No more jobs: JobQueue empty\n");
	    return undef;
	}
    }
    if(not $job->suspended()) {
	$job->set_sshlogin($sshlogin);
    }
    if(defined $opt::retries and $job->failed_here()) {
	# This command with these args failed for this sshlogin
	my ($no_of_failed_sshlogins,$min_failures) = $job->min_failed();
	# Only look at the Global::host that have > 0 jobslots
	if($no_of_failed_sshlogins ==
	   grep { $_->max_jobs_running() > 0 } values %Global::host
	   and $job->failed_here() == $min_failures) {
	    # It failed the same or more times on another host:
	    # run it on this host
	} else {
	    # If it failed fewer times on another host:
	    # Find another job to run
	    my $nextjob;
	    if(not $Global::JobQueue->empty()) {
		# This can potentially recurse for all args
		no warnings 'recursion';
		$nextjob = get_job_with_sshlogin($sshlogin);
	    }
	    # Push the command back on the queue
	    $Global::JobQueue->unget($job);
	    return $nextjob;
	}
    }
    return $job;
}


sub __REMOTE_SSH__() {}


sub read_sshloginfiles(@) {
    # Read a list of --slf's
    # Input:
    #	@files = files or symbolic file names to read
    # Returns: N/A
    for my $s (@_) {
	read_sshloginfile(expand_slf_shorthand($s));
    }
}

sub expand_slf_shorthand($) {
    # Expand --slf shorthand into a read file name
    # Input:
    #	$file = file or symbolic file name to read
    # Returns:
    #	$file = actual file name to read
    my $file = shift;
    if($file eq "-") {
	# skip: It is stdin
    } elsif($file eq "..") {
	$file = $Global::config_dir."/sshloginfile";
    } elsif($file eq ".") {
	$file = "/etc/parallel/sshloginfile";
    } elsif(not -r $file) {
	for(@Global::config_dirs) {
	    if(not -r $_."/".$file) {
		# Try prepending $PARALLEL_HOME
		::error("Cannot open $file.");
		::wait_and_exit(255);
	    } else {
		$file = $_."/".$file;
		last;
	    }
	}
    }
    return $file;
}

sub read_sshloginfile($) {
    # Read sshloginfile into @Global::sshlogin
    # Input:
    #	$file = file to read
    # Uses:
    #	@Global::sshlogin
    # Returns: N/A
    local $/ = "\n";
    my $file = shift;
    my $close = 1;
    my $in_fh;
    ::debug("init","--slf ",$file);
    if($file eq "-") {
	$in_fh = *STDIN;
	$close = 0;
    } else {
	if(not open($in_fh, "<", $file)) {
	    # Try the filename
	    ::error("Cannot open $file.");
	    ::wait_and_exit(255);
	}
    }
    while(<$in_fh>) {
	chomp;
	/^\s*#/ and next;
	/^\s*$/ and next;
	push @Global::sshlogin, $_;
    }
    if($close) {
	close $in_fh;
    }
}

sub parse_sshlogin() {
    # Parse @Global::sshlogin into %Global::host.
    # Keep only hosts that are in one of the given ssh hostgroups.
    # Uses:
    #	@Global::sshlogin
    #	$Global::minimal_command_line_length
    #	%Global::host
    #	$opt::transfer
    #	@opt::return
    #	$opt::cleanup
    #	@opt::basefile
    #	@opt::trc
    # Returns: N/A
    my @login;
    if(not @Global::sshlogin) { @Global::sshlogin = (":"); }
    for my $sshlogin (@Global::sshlogin) {
	# Split up -S sshlogin,sshlogin
	# Parse ,, and \, as , but do not split on that
	#   -S "ssh -J jump1,,jump2 host1,host2" =>
	#     ssh -J jump1,jump2 host1
	#     host2
	# Protect \, and ,, as \0
	$sshlogin =~ s/\\,|,,/\0/g;
	for my $s (split /,|\n/, $sshlogin) {
	    # Replace \0 => ,
	    $s =~ s/\0/,/g;
	    if ($s eq ".." or $s eq "-") {
		# This may add to @Global::sshlogin - possibly bug
		read_sshloginfile(expand_slf_shorthand($s));
	    } else {
		$s =~ s/\s*$//;
		push (@login, $s);
	    }
	}
    }
    $Global::minimal_command_line_length = 100_000_000;
    my @allowed_hostgroups;
    for my $ncpu_sshlogin_string (::uniq(@login)) {
	my $sshlogin = SSHLogin->new($ncpu_sshlogin_string);
	my $sshlogin_string = $sshlogin->string();
	if($sshlogin_string eq "") {
	    # This is an ssh group: -S @webservers
	    push @allowed_hostgroups, $sshlogin->hostgroups();
	    next;
	}
	if($Global::host{$sshlogin_string}) {
	    # This sshlogin has already been added:
	    # It is probably a host that has come back
	    # Set the max_jobs_running back to the original
	    debug("run","Already seen $sshlogin_string\n");
	    if($sshlogin->{'ncpus'}) {
		# If ncpus set by '#/' of the sshlogin, overwrite it:
		$Global::host{$sshlogin_string}->set_ncpus($sshlogin->ncpus());
	    }
	    $Global::host{$sshlogin_string}->set_max_jobs_running(undef);
	    next;
	}
	$sshlogin->set_maxlength(Limits::Command::max_length());

	$Global::minimal_command_line_length =
	    ::min($Global::minimal_command_line_length, $sshlogin->maxlength());
	$Global::host{$sshlogin_string} = $sshlogin;
    }
    $Global::usable_command_line_length =
	# Usable len = maxlen - 3000 for wrapping, div 2 for hexing
	int(($Global::minimal_command_line_length - 3000)/2);
    if($opt::max_chars) {
	if($opt::max_chars <= $Global::usable_command_line_length) {
	    $Global::usable_command_line_length = $opt::max_chars;
	} else {
	    ::warning("Value for option -s should be < ".
		      $Global::usable_command_line_length.".");
	}
    }
    if(@allowed_hostgroups) {
	# Remove hosts that are not in these groups
	while (my ($string, $sshlogin) = each %Global::host) {
	    if(not $sshlogin->in_hostgroups(@allowed_hostgroups)) {
		delete $Global::host{$string};
	    }
	}
    }

    # debug("start", "sshlogin: ", my_dump(%Global::host),"\n");
    if(@Global::transfer_files or @opt::return
       or $opt::cleanup or @opt::basefile) {
	if(not remote_hosts()) {
	    # There are no remote hosts
	    if(@opt::trc) {
		::warning("--trc ignored as there are no remote --sshlogin.");
	    } elsif (defined $opt::transfer) {
		::warning("--transfer ignored as there are ".
			  "no remote --sshlogin.");
	    } elsif (@opt::transfer_files) {
		::warning("--transferfile ignored as there ".
			  "are no remote --sshlogin.");
	    } elsif (@opt::return) {
		::warning("--return ignored as there are no remote --sshlogin.");
	    } elsif (defined $opt::cleanup and not %opt::template) {
		::warning("--cleanup ignored as there ".
			  "are no remote --sshlogin.");
	    } elsif (@opt::basefile) {
		::warning("--basefile ignored as there ".
			  "are no remote --sshlogin.");
	    }
	}
    }
}

sub remote_hosts() {
    # Return sshlogins that are not ':'
    # Uses:
    #	%Global::host
    # Returns:
    #	list of sshlogins with ':' removed
    return grep !/^:$/, keys %Global::host;
}

sub setup_basefile() {
    # Transfer basefiles to each $sshlogin
    # This needs to be done before first jobs on $sshlogin is run
    # Uses:
    #	%Global::host
    #	@opt::basefile
    # Returns: N/A
    my @cmd;
    my $rsync_destdir;
    my $workdir;
    for my $sshlogin (values %Global::host) {
      if($sshlogin->local()) { next }
      for my $file (@opt::basefile) {
	if($file !~ m:^/: and $opt::workdir eq "...") {
	  ::error("Work dir '...' will not work with relative basefiles.");
	  ::wait_and_exit(255);
	}
	if(not $workdir) {
	    my $dummycmdline =
		CommandLine->new(1,["true"],{},0,0,[],[],[],[],{},{});
	    my $dummyjob = Job->new($dummycmdline);
	    $workdir = $dummyjob->workdir();
	}
	push @cmd, $sshlogin->rsync_transfer_cmd($file,$workdir);
      }
    }
    debug("init", "basesetup: @cmd\n");
    my ($exitstatus,$stdout_ref,$stderr_ref) =
	run_gnu_parallel((join "\n",@cmd),"-j0","--retries",5);
    if($exitstatus) {
	my @stdout = @$stdout_ref;
	my @stderr = @$stderr_ref;
	::error("Copying of --basefile failed: @stdout@stderr");
	::wait_and_exit(255);
    }
}

sub cleanup_basefile() {
    # Remove the basefiles transferred
    # Uses:
    #	%Global::host
    #	@opt::basefile
    # Returns: N/A
    my @cmd;
    my $workdir;
    if(not $workdir) {
	my $dummycmdline = CommandLine->new(1,["true"],{},0,0,[],[],[],[],{},{});
	my $dummyjob = Job->new($dummycmdline);
	$workdir = $dummyjob->workdir();
    }
    for my $sshlogin (values %Global::host) {
	if($sshlogin->local()) { next }
	for my $file (@opt::basefile) {
	    push @cmd, $sshlogin->cleanup_cmd($file,$workdir);
	}
    }
    debug("init", "basecleanup: @cmd\n");
    my ($exitstatus,$stdout_ref,$stderr_ref) =
	run_gnu_parallel(join("\n",@cmd),"-j0","--retries",5);
    if($exitstatus) {
	my @stdout = @$stdout_ref;
	my @stderr = @$stderr_ref;
	::error("Cleanup of --basefile failed: @stdout@stderr");
	::wait_and_exit(255);
    }
}

sub run_gnu_parallel() {
    my ($stdin,@args) = @_;
    my $cmd = join "",map { " $_ & " } split /\n/, $stdin;
    print $Global::original_stderr ` $cmd wait` ;
    return 0
}

sub _run_gnu_parallel() {
    # Run GNU Parallel
    # This should ideally just fork an internal copy
    # and not start it through a shell
    # Input:
    #	$stdin = data to provide on stdin for GNU   Parallel
    #	@args = command line arguments
    # Returns:
    #	$exitstatus = exitcode of GNU Parallel run
    #	\@stdout = standard output
    #	\@stderr = standard error
    my ($stdin,@args) = @_;
    my ($exitstatus,@stdout,@stderr);
    my ($stdin_fh,$stdout_fh)=(gensym(),gensym());
    my ($stderr_fh, $stderrname) = ::tmpfile(SUFFIX => ".par");
    unlink $stderrname;

    my $pid = ::open3($stdin_fh,$stdout_fh,$stderr_fh,
		      $0,qw(--plain --shell /bin/sh --will-cite), @args);
    if(my $writerpid = fork()) {
	close $stdin_fh;
	@stdout = <$stdout_fh>;
	# Now stdout is closed:
	# These pids should be dead or die very soon
	while(kill 0, $writerpid) { ::usleep(1); }
	die;
#	reap $writerpid;
#	while(kill 0, $pid) { ::usleep(1); }
#	reap $writerpid;
	$exitstatus = $?;
	seek $stderr_fh, 0, 0;
	@stderr = <$stderr_fh>;
	close $stdout_fh;
	close $stderr_fh;
    } else {
	close $stdout_fh;
	close $stderr_fh;
	print $stdin_fh $stdin;
	close $stdin_fh;
	exit(0);
    }
    return ($exitstatus,\@stdout,\@stderr);
}

sub filter_hosts() {
    # Remove down --sshlogins from active duty.
    # Find ncpus, ncores, maxlen, time-to-login for each host.
    # Uses:
    #	%Global::host
    #	$Global::minimal_command_line_length
    #	$opt::use_sockets_instead_of_threads
    #	$opt::use_cores_instead_of_threads
    #	$opt::use_cpus_instead_of_cores
    # Returns: N/A

    my ($nsockets_ref,$ncores_ref, $nthreads_ref, $time_to_login_ref,
	$maxlen_ref, $echo_ref, $down_hosts_ref) =
	parse_host_filtering(parallelized_host_filtering());

    delete @Global::host{@$down_hosts_ref};
    @$down_hosts_ref and ::warning("Removed @$down_hosts_ref.");

    $Global::minimal_command_line_length = 100_000_000;
    while (my ($string, $sshlogin) = each %Global::host) {
	if($sshlogin->local()) { next }
	my ($nsockets,$ncores,$nthreads,$time_to_login,$maxlen) =
	    ($nsockets_ref->{$string},$ncores_ref->{$string},
	     $nthreads_ref->{$string},$time_to_login_ref->{$string},
	     $maxlen_ref->{$string});
	defined $nsockets or ::die_bug("nsockets missing: $string");
	defined $ncores or ::die_bug("ncores missing: $string");
	defined $nthreads or ::die_bug("nthreads missing: $string");
	defined $time_to_login or ::die_bug("time_to_login missing: $string");
	defined $maxlen or ::die_bug("maxlen missing: $string");
	# ncpus may be set by 4/hostname or may be undefined yet
	my $ncpus = $sshlogin->{'ncpus'};
	# $nthreads may be 0 if GNU Parallel is not installed remotely
	$ncpus = $nthreads || $ncpus || $sshlogin->ncpus();
	if($opt::use_cpus_instead_of_cores) {
	    $ncpus = $ncores || $ncpus;
	} elsif($opt::use_sockets_instead_of_threads) {
	    $ncpus = $nsockets || $ncpus;
	} elsif($opt::use_cores_instead_of_threads) {
	    $ncpus = $ncores || $ncpus;
	}
	$sshlogin->set_ncpus($ncpus);
	$sshlogin->set_time_to_login($time_to_login);
	$maxlen = $maxlen || Limits::Command::max_length();
	$sshlogin->set_maxlength($maxlen);
	::debug("init", "Timing from -S:$string ",
		" ncpus:", $ncpus,
		" nsockets:",$nsockets,
		" ncores:", $ncores,
		" nthreads:",$nthreads,
		" time_to_login:", $time_to_login,
		" maxlen:", $maxlen,
		" min_max_len:", $Global::minimal_command_line_length,"\n");
    }
}

sub parse_host_filtering() {
    # Input:
    #	@lines = output from parallelized_host_filtering()
    # Returns:
    #	\%nsockets = number of sockets of {host}
    #	\%ncores = number of cores of {host}
    #	\%nthreads = number of hyperthreaded cores of {host}
    #	\%time_to_login = time_to_login on {host}
    #	\%maxlen = max command len on {host}
    #	\%echo = echo received from {host}
    #	\@down_hosts = list of hosts with no answer
    local $/ = "\n";
    my (%nsockets, %ncores, %nthreads, %time_to_login, %maxlen, %echo,
	@down_hosts);
    for (@_) {
	::debug("init","Read: ",$_);
	chomp;
	my @col = split /\t/, $_;
	if($col[0] =~ /^parallel: Warning:/) {
	    # Timed out job: Ignore it
	    next;
	} elsif(defined $col[6]) {
	    # This is a line from --joblog
	    # seq host time spent sent received exit signal command
	    # 2 : 1372607672.654 0.675 0 0 0 0 eval true\ m\;ssh\ m\ parallel\ --number-of-cores
	    if($col[0] eq "Seq" and $col[1] eq "Host" and
		    $col[2] eq "Starttime") {
		# Header => skip
		next;
	    }
	    # Get server from: eval true server\;
	    $col[8] =~ /eval .?true.?\s([^\;]+);/ or
		::die_bug("col8 does not contain host: $col[8] in $_");
	    my $host = $1;
	    $host =~ tr/\\//d;
	    $Global::host{$host} or next;
	    if($col[6] eq "255" or $col[6] eq "-1" or $col[6] eq "1") {
		# exit == 255 or exit == timeout (-1): ssh failed/timedout
		# exit == 1: lsh failed
		# Remove sshlogin
		::debug("init", "--filtered $host\n");
		push(@down_hosts, $host);
	    } elsif($col[6] eq "127") {
		# signal == 127: parallel not installed remote
		# Set nsockets, ncores, nthreads = 1
		::warning("Could not figure out ".
			  "number of cpus on $host. Using 1.");
		$nsockets{$host} = 1;
		$ncores{$host} = 1;
		$nthreads{$host} = 1;
		$maxlen{$host} = Limits::Command::max_length();
	    } elsif($col[0] =~ /^\d+$/ and $Global::host{$host}) {
		# Remember how log it took to log in
		# 2 : 1372607672.654 0.675 0 0 0 0 eval true\ m\;ssh\ m\ echo
		$time_to_login{$host} = ::min($time_to_login{$host},$col[3]);
	    } else {
		::die_bug("host check unmatched long jobline: $_");
	    }
	} elsif($Global::host{$col[0]}) {
	    # This output from --number-of-cores, --number-of-cpus,
	    # --max-line-length-allowed
	    # ncores: server	   8
	    # ncpus:  server	   2
	    # maxlen: server	   131071
	    if(/parallel: Warning: Cannot figure out number of/) {
		next;
	    }
	    if(/\t(perl: warning:|LANGUAGE =|LC_ALL =|LANG =|are supported and installed|Disconnected from|Received disconnect from)/
	       or
	       /\tWarning: /
	       or
	       /\t(Host key fingerprint is|\+-.*-\+|\|.*\|)/
	       or
	       /\t\S+: Undefined variable./
		) {
		# Skip these (from perl):
		#   perl: warning: Setting locale failed.
		#   perl: warning: Please check that your locale settings:
		#   	  LANGUAGE = (unset),
		#   	  LC_ALL = (unset),
		#   	  LANG = "en_US.UTF-8"
		#       are supported and installed on your system.
		#   perl: warning: Falling back to the standard locale ("C").
		#   Disconnected from 127.0.0.1 port 22
		#
		# Skip these (from ssh):
		#   Warning: Permanently added * to the list of known hosts.
		#   Warning: Identity file * not accessible: *
		#   (VisualHostKey=yes)
		#   Host key fingerprint is SHA256:...
		#   +--[ED25519 256]--+
		#   |               o |
		#   +----[SHA256]-----+
		#
		# Skip these (from csh):
		#   MANPATH: Undefined variable.
	    } elsif(not defined $nsockets{$col[0]}) {
		$nsockets{$col[0]} = $col[1];
	    } elsif(not defined $ncores{$col[0]}) {
		$ncores{$col[0]} = $col[1];
	    } elsif(not defined $nthreads{$col[0]}) {
		$nthreads{$col[0]} = $col[1];
	    } elsif(not defined $maxlen{$col[0]}) {
		$maxlen{$col[0]} = $col[1];
	    } elsif(not defined $echo{$col[0]}) {
		$echo{$col[0]} = $col[1];
	    } else {
		::die_bug("host check too many col0: $_");
	    }
	} else {
	    ::die_bug("host check unmatched short jobline ($col[0]): $_");
	}
    }
    @down_hosts = uniq(@down_hosts);
    return(\%nsockets, \%ncores, \%nthreads, \%time_to_login,
	   \%maxlen, \%echo, \@down_hosts);
}

sub parallelized_host_filtering() {
    # Uses:
    #	%Global::host
    # Returns:
    #	text entries with:
    #	* joblog line
    #	* hostname \t number of cores
    #	* hostname \t number of cpus
    #	* hostname \t max-line-length-allowed
    #	* hostname \t empty

    sub sshwrapped {
	# Wrap with ssh and --env
	# Return $default_value if command fails
	my $sshlogin = shift;
	my $command = shift;
	# wrapper that returns output "0\n" if the command fails
	# E.g. parallel not installed => "0\n"
	my $wcmd = q(perl -e '$a=`).$command.q(`; print $? ? "0".v010 : $a');
	my $commandline = CommandLine->new(1,[$wcmd],{},0,0,[],[],[],[],{},{});
	my $job = Job->new($commandline);
	$job->set_sshlogin($sshlogin);
	$job->wrapped();
	return($job->{'wrapped'});
    }

    my(@sockets, @cores, @threads, @maxline, @echo);
    while (my ($host, $sshlogin) = each %Global::host) {
	if($host eq ":") { next }
	# The 'true' is used to get the $host out later
	push(@sockets, $host."\t"."true $host; ".
	     sshwrapped($sshlogin,"parallel --number-of-sockets")."\n\0");
	push(@cores, $host."\t"."true $host; ".
	     sshwrapped($sshlogin,"parallel --number-of-cores")."\n\0");
	push(@threads, $host."\t"."true $host; ".
	     sshwrapped($sshlogin,"parallel --number-of-threads")."\n\0");
	push(@maxline, $host."\t"."true $host; ".
	     sshwrapped($sshlogin,
			"parallel --max-line-length-allowed")."\n\0");
	# 'echo' is used to get the fastest possible ssh login time
	push(@echo, $host."\t"."true $host; ".
	     $sshlogin->wrap("echo $host")."\n\0");
    }
    # --timeout 10: Setting up an SSH connection and running a simple
    #		    command should never take > 10 sec.
    # --delay 0.1:  If multiple sshlogins use the same proxy the delay
    #		    will make it less likely to overload the ssh daemon.
    # --retries 3:  If the ssh daemon is overloaded, try 3 times
    my $cmd =
	"$0 -j0 --timeout 10 --joblog - --plain --delay 0.1 --retries 3 ".
	"--tag --tagstring '{1}' -0 --colsep '\t' -k eval '{2}' && true ";
    $cmd = $Global::shell." -c ".Q($cmd);
    ::debug("init", $cmd, "\n");
    my @out;
    my $prepend = "";

    my ($host_fh,$in,$err);
    open3($in, $host_fh, $err, $cmd) || ::die_bug("parallel host check: $cmd");
    ::debug("init", map { $_,"\n" } @sockets, @cores, @threads, @maxline, @echo);

    if(not fork()) {
	# Give the commands to run to the $cmd
	close $host_fh;
	print $in @sockets, @cores, @threads, @maxline, @echo;
	close $in;
	exit();
    }
    close $in;
    # If -0: $/ must be \n
    local $/ = "\n";
    for(<$host_fh>) {
	# TODO incompatible with '-quoting. Needs to be fixed differently
	#if(/\'$/) {
	#    # if last char = ' then append next line
	#    # This may be due to quoting of \n in environment var
	#    $prepend .= $_;
	#    next;
	#}
	$_ = $prepend . $_;
	$prepend = "";
	push @out, $_;
    }
    close $host_fh;
    return @out;
}

sub onall($@) {
    # Runs @command on all hosts.
    # Uses parallel to run @command on each host.
    # --jobs = number of hosts to run on simultaneously.
    # For each host a parallel command with the args will be running.
    # Uses:
    #	$Global::debug
    #	$Global::exitstatus
    #	$Global::joblog
    #	$Global::quoting
    #	$opt::D
    #	$opt::arg_file_sep
    #	$opt::arg_sep
    #	$opt::colsep
    #	$opt::files
    #	$opt::files0
    #	$opt::group
    #	$opt::joblog
    #	$opt::jobs
    #	$opt::keeporder
    #	$opt::linebuffer
    #	$opt::max_chars
    #	$opt::plain
    #	$opt::retries
    #	$opt::tag
    #	$opt::tee
    #	$opt::timeout
    #	$opt::ungroup
    #	%Global::host
    #	@opt::basefile
    #	@opt::env
    #	@opt::v
    # Input:
    #	@command = command to run on all hosts
    # Returns: N/A
    sub tmp_joblog {
	# Input:
	#   $joblog = filename of joblog - undef if none
	# Returns:
	#   $tmpfile = temp file for joblog - undef if none
	my $joblog = shift;
	if(not defined $joblog) {
	    return undef;
	}
	my ($fh, $tmpfile) = ::tmpfile(SUFFIX => ".log");
	close $fh;
	return $tmpfile;
    }
    my ($input_source_fh_ref,@command) = @_;
    if($Global::quoting) {
       @command = shell_quote(@command);
    }

    # Copy all @input_source_fh (-a and :::) into tempfiles
    my @argfiles = ();
    for my $fh (@$input_source_fh_ref) {
	my ($outfh, $name) = ::tmpfile(SUFFIX => ".all", UNLINK => not $opt::D);
	print $outfh (<$fh>);
	close $outfh;
	push @argfiles, $name;
    }
    if(@opt::basefile) { setup_basefile(); }
    # for each sshlogin do:
    # parallel -S $sshlogin $command :::: @argfiles
    #
    # Pass some of the options to the sub-parallels, not all of them as
    # -P should only go to the first, and -S should not be copied at all.
    my $options =
	join(" ",
	     ((defined $opt::sshdelay) ? "--delay ".$opt::sshdelay : ""),
	     ((defined $opt::memfree) ? "--memfree ".$opt::memfree : ""),
	     ((defined $opt::memsuspend) ? "--memfree ".$opt::memsuspend : ""),
	     ((defined $opt::D) ? "-D $opt::D" : ""),
	     ((defined $opt::group) ? "--group" : ""),
	     ((defined $opt::jobs) ? "-P $opt::jobs" : ""),
	     ((defined $opt::keeporder) ? "--keeporder" : ""),
	     ((defined $opt::linebuffer) ? "--linebuffer" : ""),
	     ((defined $opt::max_chars) ? "--max-chars ".$opt::max_chars : ""),
	     ((defined $opt::plain) ? "--plain" : ""),
	     (($opt::ungroup == 1) ? "-u" : ""),
	     ((defined $opt::tee) ? "--tee" : ""),
	);
    my $suboptions =
	join(" ",
	     ((defined $opt::sshdelay) ? "--delay ".$opt::sshdelay : ""),
	     ((defined $opt::D) ? "-D $opt::D" : ""),
	     ((defined $opt::arg_file_sep) ? "--arg-file-sep ".$opt::arg_file_sep : ""),
	     ((defined $opt::arg_sep) ? "--arg-sep ".$opt::arg_sep : ""),
	     ((defined $opt::colsep) ? "--colsep ".shell_quote($opt::colsep) : ""),
	     ((defined $opt::files) ? "--files" : ""),
	     ((defined $opt::files0) ? "--files0" : ""),
	     ((defined $opt::group) ? "--group" : ""),
	     ((defined $opt::cleanup) ? "--cleanup" : ""),
	     ((defined $opt::keeporder) ? "--keeporder" : ""),
	     ((defined $opt::linebuffer) ? "--linebuffer" : ""),
	     ((defined $opt::max_chars) ? "--max-chars ".$opt::max_chars : ""),
	     ((defined $opt::plain) ? "--plain" : ""),
	     ((defined $opt::plus) ? "--plus" : ""),
	     ((defined $opt::retries) ? "--retries ".$opt::retries : ""),
	     ((defined $opt::timeout) ? "--timeout ".$opt::timeout : ""),
	     (($opt::ungroup == 1) ? "-u" : ""),
	     ((defined $opt::ssh) ? "--ssh '".$opt::ssh."'" : ""),
	     ((defined $opt::tee) ? "--tee" : ""),
	     ((defined $opt::workdir) ? "--wd ".Q($opt::workdir) : ""),
	     (@Global::transfer_files ? map { "--tf ".Q($_) }
	      @Global::transfer_files : ""),
	     (@Global::ret_files ? map { "--return ".Q($_) }
	      @Global::ret_files : ""),
	     (@opt::env ? map { "--env ".Q($_) } @opt::env : ""),
	     (map { "-v" } @opt::v),
	);
    ::debug("init", "| $0 $options\n");
    open(my $parallel_fh, "|-", "$0 -0 --will-cite -j0 $options") ||
	::die_bug("This does not run GNU Parallel: $0 $options");
    my @joblogs;
    for my $host (sort keys %Global::host) {
	my $sshlogin = $Global::host{$host};
	my $qsshlogin = Q($sshlogin->string());
	my $joblog = tmp_joblog($opt::joblog);
	if($joblog) {
	    push @joblogs, $joblog;
	    $joblog = "--joblog ".::Q($joblog);
	}
	my $quad = $opt::arg_file_sep || "::::";
	# If PARALLEL_ENV is set: Pass it on
	my $penv=$Global::parallel_env ?
	    "PARALLEL_ENV=".Q($Global::parallel_env) :
	    '';
	my $results;
	if(defined $opt::results) {
	    $results = Q($opt::results) . $qsshlogin;
	}
	::debug("init", "$penv $0 $suboptions -j1 $joblog ",
		((defined $opt::tag) ? "--tagstring ".$qsshlogin : ""),
		((defined $opt::results) ? "--results ".$results : ""),
		" -S $qsshlogin ",
		join(" ",shell_quote(@command,$quad,@argfiles)),"\n");
	print $parallel_fh "$penv $0 $suboptions -j1 $joblog ",
	    ((defined $opt::tag) ? "--tagstring ".$qsshlogin : ""),
	    ((defined $opt::results) ? "--results ".$results : ""),
	    " -S $qsshlogin ",
	    join(" ",shell_quote(@command,$quad,@argfiles)),"\0";
    }
    close $parallel_fh;
    $Global::exitstatus = $? >> 8;
    debug("init", "--onall exitvalue ", $?);
    if(@opt::basefile and $opt::cleanup) { cleanup_basefile(); }
    $Global::debug or unlink(@argfiles);
    my %seen;
    for my $joblog (@joblogs) {
	# Append to $joblog
	open(my $fh, "<", $joblog) ||
	    ::die_bug("Cannot open tmp joblog $joblog");
	# Skip first line (header);
	<$fh>;
	print $Global::joblog (<$fh>);
	close $fh;
	unlink($joblog);
    }
}


sub __SIGNAL_HANDLING__() {}


sub sigtstp() {
    # Send TSTP signal (Ctrl-Z) to all children process groups
    # Uses:
    #	%SIG
    # Returns: N/A
    signal_children("TSTP");
}

sub sigpipe() {
    # Send SIGPIPE signal to all children process groups
    # Uses:
    #	%SIG
    # Returns: N/A
    signal_children("PIPE");
}

sub signal_children() {
    # Send signal to all children process groups
    # and GNU	Parallel itself
    # Uses:
    #	%SIG
    # Returns: N/A
    my $signal = shift;
    debug("run", "Sending $signal ");
    kill $signal, map { -$_ } keys %Global::running;
    # Use default signal handler for GNU Parallel itself
    $SIG{$signal} = undef;
    kill $signal, $$;
}

sub save_original_signal_handler() {
    # Remember the original signal handler
    # Uses:
    #	%Global::original_sig
    # Returns: N/A
    $SIG{INT} = sub {
	if($opt::tmux) { ::qqx("tmux kill-session -t p$$"); }
	wait_and_exit(255);
    };
    $SIG{TERM} = sub {
	if($opt::tmux) { ::qqx("tmux kill-session -t p$$"); }
	wait_and_exit(255);
    };
    %Global::original_sig = %SIG;
    $SIG{TERM} = sub {}; # Dummy until jobs really start
    $SIG{ALRM} = 'IGNORE';
    # Allow Ctrl-Z to suspend and `fg` to continue
    $SIG{TSTP} = \&sigtstp;
    $SIG{PIPE} = \&sigpipe;
    $SIG{CONT} = sub {
	# Set $SIG{TSTP} again (it is undef'ed in sigtstp() )
	$SIG{TSTP} = \&sigtstp;
	for my $job (values %Global::running) {
	    if($job->suspended()) {
		# Force jobs to suspend, if they are marked as suspended.
		# --memsupspend can suspend a job that will be resumed
		# if the user presses CTRL-Z followed by `fg`.
		$job->suspend();
	    } else {
		# Resume the rest of the jobs
		$job->resume();
	    }
	}
    };
}

sub list_running_jobs() {
    # Print running jobs on tty
    # Uses:
    #	%Global::running
    # Returns: N/A
    for my $job (values %Global::running) {
	::status("$Global::progname: ".$job->replaced());
    }
}

sub start_no_new_jobs() {
    # Start no more jobs
    # Uses:
    #	 %Global::original_sig
    #	 %Global::unlink
    #	 $Global::start_no_new_jobs
    # Returns: N/A
    unlink keys %Global::unlink;
    ::status
	("$Global::progname: SIGHUP received. No new jobs will be started.",
	 "$Global::progname: Waiting for these ".(keys %Global::running).
	 " jobs to finish. Send SIGTERM to stop now.");
    list_running_jobs();
    $Global::start_no_new_jobs ||= 1;
}

sub reapers() {
    # Run reaper until there are no more left
    # Returns:
    #	@pids_reaped = pids of reaped processes
    my @pids_reaped;
    my $pid;
    while($pid = reaper()) {
	push @pids_reaped, $pid;
    }
    return @pids_reaped;
}

sub reaper() {
    # A job finished:
    # * Set exitstatus, exitsignal, endtime.
    # * Free ressources for new job
    # * Update median runtime
    # * Print output
    # * If --halt = now: Kill children
    # * Print progress
    # Uses:
    #	%Global::running
    #	$opt::timeout
    #	$Global::timeoutq
    #	$opt::keeporder
    #	$Global::total_running
    # Returns:
    #	$stiff = PID of child finished
    my $stiff;
    debug("run", "Reaper ");
    if(($stiff = waitpid(-1, &WNOHANG)) <= 0) {
	# No jobs waiting to be reaped
	return 0;
    }

    # $stiff = pid of dead process
    my $job = $Global::running{$stiff};

    # '-a <(seq 10)' will give us a pid not in %Global::running
    # The same will one of the ssh -M: ignore
    $job or return 0;
    delete $Global::running{$stiff};
    $Global::total_running--;
    if($job->{'commandline'}{'skip'}) {
	# $job->skip() was called
	$job->set_exitstatus(-2);
	$job->set_exitsignal(0);
    } else {
	$job->set_exitsignal($? & 127);
	if($job->exitstatus()) {
	    # Exit status already set - probably by --timeout
	} elsif($? & 127) {
	    # Killed by signal. Many shells return: 128 | $signal
	    $job->set_exitstatus(128 | $?);
	} else {
	    # Normal exit
	    $job->set_exitstatus($? >> 8);
	}
    }

    debug("run", "\nseq ",$job->seq()," died (", $job->exitstatus(), ")");
    if($Global::delayauto or $Global::sshdelayauto) {
	if($job->exitstatus()) {
	    # Job failed: Increase delay (if $opt::(ssh)delay set)
	    $opt::delay &&= $opt::delay * 1.3;
	    $opt::sshdelay &&= $opt::sshdelay * 1.3;
	} else {
	    # Job succeeded: Decrease delay (if $opt::(ssh)delay set)
	    $opt::delay &&= $opt::delay * 0.9;
	    $opt::sshdelay &&= $opt::sshdelay * 0.9;
	}
	debug("run", "delay:$opt::delay ssh:$opt::sshdelay ");
    }
    $job->set_endtime(::now());
    my $sshlogin = $job->sshlogin();
    $sshlogin->dec_jobs_running();
    if($job->should_be_retried()) {
	# Free up file handles
	$job->free_ressources();
    } else {
	# The job is done
	$sshlogin->inc_jobs_completed();
	# Free the jobslot
	$job->free_slot();
	if($opt::timeout and not $job->exitstatus()) {
	    # Update average runtime for timeout only for successful jobs
	    $Global::timeoutq->update_median_runtime($job->runtime());
	}
	if($opt::keeporder and not $opt::latestline) {
	    # --latestline fixes --keeporder in Job::row()
	    $job->print_earlier_jobs();
	} else {
	    $job->print();
	}
	if($job->should_we_halt() eq "now") {
	    # Kill children
	    ::kill_sleep_seq($job->pid());
	    ::killall();
	    ::wait_and_exit($Global::halt_exitstatus);
	}
    }
    $job->cleanup();

    if($opt::progress) {
	my %progress = progress();
	::status_no_nl("\r",$progress{'status'});
    }

    debug("run", "jobdone \n");
    return $stiff;
}


sub __USAGE__() {}


sub killall() {
    # Kill all jobs by killing their process groups
    # Uses:
    #	$Global::start_no_new_jobs = we are stopping
    #	$Global::killall = Flag to not run reaper
    $Global::start_no_new_jobs ||= 1;
    # Do not reap killed children: Ignore them instead
    $Global::killall ||= 1;
    kill_sleep_seq(keys %Global::running);
}

sub kill_sleep_seq(@) {
    # Send jobs TERM,TERM,KILL to processgroups
    # Input:
    #	@pids = list of pids that are also processgroups
    # Convert pids to process groups ($processgroup = -$pid)
    my @pgrps = map { -$_ } @_;
    my @term_seq = split/,/,$opt::termseq;
    if(not @term_seq) {
	@term_seq = ("TERM",200,"TERM",100,"TERM",50,"KILL",25);
    }
    # for each signal+waittime: kill process groups still not dead
    while(@term_seq) {
	@pgrps = kill_sleep(shift @term_seq, shift @term_seq, @pgrps);
    }
}

sub kill_sleep() {
    # Kill pids with a signal and wait a while for them to die
    # Input:
    #	$signal = signal to send to @pids
    #	$sleep_max = number of ms to sleep at most before returning
    #	@pids = pids to kill (actually process groups)
    # Uses:
    #	$Global::killall = set by killall() to avoid calling reaper
    # Returns:
    #	@pids = pids still alive
    my ($signal, $sleep_max, @pids) = @_;
    ::debug("kill","kill_sleep $signal ",(join " ",sort @pids),"\n");
    kill $signal, @pids;
    my $sleepsum = 0;
    my $sleep = 0.001;

    while(@pids and $sleepsum < $sleep_max) {
	if($Global::killall) {
	    # Killall => don't run reaper
	    while(waitpid(-1, &WNOHANG) > 0) {
		$sleep = $sleep/2+0.001;
	    }
	} elsif(reapers()) {
	    $sleep = $sleep/2+0.001;
	}
	$sleep *= 1.1;
	::usleep($sleep);
	$sleepsum += $sleep;
	# Keep only living children
	@pids = grep { kill(0, $_) } @pids;
    }
    return @pids;
}

sub wait_and_exit($) {
    # If we do not wait, we sometimes get segfault
    # Returns: N/A
    my $error = shift;
    unlink keys %Global::unlink;
    if($error) {
	# Kill all jobs without printing
	killall();
    }
    for (keys %Global::unkilled_children) {
	# Kill any (non-jobs) children (e.g. reserved processes)
	kill 9, $_;
	waitpid($_,0);
	delete $Global::unkilled_children{$_};
    }
    if($Global::unkilled_sqlworker) {
	waitpid($Global::unkilled_sqlworker,0);
    }
    # Avoid: Warning: unable to close filehandle properly: No space
    #	     left on device during global destruction.
    $SIG{__WARN__} = sub {};
    if($opt::_parset) {
	# Make the shell script return $error
	print "$Global::parset_endstring\nreturn $error";
    }
    exit($error);
}

sub die_usage() {
    # Returns: N/A
    usage();
    wait_and_exit(255);
}

sub usage() {
    # Returns: N/A
    print join
	("\n",
	 "Usage:",
	 "",
	 "$Global::progname [options] [command [arguments]] < list_of_arguments",
	 "$Global::progname [options] [command [arguments]] (::: arguments|:::: argfile(s))...",
	 "cat ... | $Global::progname --pipe [options] [command [arguments]]",
	 "",
	 "-j n            Run n jobs in parallel",
	 "-k              Keep same order",
	 "-X              Multiple arguments with context replace",
	 "--colsep regexp Split input on regexp for positional replacements",
	 "{} {.} {/} {/.} {#} {%} {= perl code =} Replacement strings",
	 "{3} {3.} {3/} {3/.} {=3 perl code =}    Positional replacement strings",
	 "With --plus:    {} = {+/}/{/} = {.}.{+.} = {+/}/{/.}.{+.} = {..}.{+..} =",
	 "                {+/}/{/..}.{+..} = {...}.{+...} = {+/}/{/...}.{+...}",
	 "",
	 "-S sshlogin     Example: foo\@server.example.com",
	 "--slf ..        Use ~/.parallel/sshloginfile as the list of sshlogins",
	 "--trc {}.bar    Shorthand for --transfer --return {}.bar --cleanup",
	 "--onall         Run the given command with argument on all sshlogins",
	 "--nonall        Run the given command with no arguments on all sshlogins",
	 "",
	 "--pipe          Split stdin (standard input) to multiple jobs.",
	 "--recend str    Record end separator for --pipe.",
	 "--recstart str  Record start separator for --pipe.",
	 "",
	 "GNU Parallel can do much more. See 'man $Global::progname' for details",
	 "",
	 "Academic tradition requires you to cite works you base your article on.",
	 "If you use programs that use GNU Parallel to process data for an article in a",
	 "scientific publication, please cite:",
	 "",
	 "  Tange, O. (2023, August 22). GNU Parallel 20230822 ('Chandrayaan').",
	 "  Zenodo. https://doi.org/10.5281/zenodo.8278274",
	 "",
	 # Before changing these lines, please read
	 # https://www.gnu.org/software/parallel/parallel_design.html#citation-notice
	 # https://git.savannah.gnu.org/cgit/parallel.git/tree/doc/citation-notice-faq.txt
	 # You accept to be put in a  public hall of shame  by removing
	 # these lines
	 "This helps funding further development; AND IT WON'T COST YOU A CENT.",
	 "If you pay 10000 EUR you should feel free to use GNU Parallel without citing.",
	 "",
	 "",);
}

sub citation_notice() {
    # if --will-cite or --plain: do nothing
    # if stderr redirected: do nothing
    # if $PARALLEL_HOME/will-cite: do nothing
    # else: print citation notice to stderr
    if($opt::willcite
       or
       $opt::plain
       or
       not -t $Global::original_stderr
       or
       grep { -e "$_/will-cite" } @Global::config_dirs) {
	# skip
    } else {
	::status
	    ("Academic tradition requires you to cite works you base your article on.",
	     "If you use programs that use GNU Parallel to process data for an article in a",
	     "scientific publication, please cite:",
	     "",
	     "  Tange, O. (2023, August 22). GNU Parallel 20230822 ('Chandrayaan').",
	     "  Zenodo. https://doi.org/10.5281/zenodo.8278274",
	     "",
	     # Before changing these line,  please read
	     # https://www.gnu.org/software/parallel/parallel_design.html#citation-notice and
	     # https://git.savannah.gnu.org/cgit/parallel.git/tree/doc/citation-notice-faq.txt
	     # You accept to be put in a public hall of shame by
	     # removing these lines
	     "This helps funding further development; AND IT WON'T COST YOU A CENT.",
	     "If you pay 10000 EUR you should feel free to use GNU Parallel without citing.",
	     "",
	     "More about funding GNU Parallel and the citation notice:",
	     "https://www.gnu.org/software/parallel/parallel_design.html#citation-notice",
	     "",
	     "To silence this citation notice: run 'parallel --citation' once.",
	     ""
	    );
	mkdir $Global::config_dir;
	# Number of times the user has run GNU Parallel without showing
	# willingness to cite
	my $runs = 0;
	if(open (my $fh, "<", $Global::config_dir.
		 "/runs-without-willing-to-cite")) {
	    $runs = <$fh>;
	    close $fh;
	}
	$runs++;
	if(open (my $fh, ">", $Global::config_dir.
		 "/runs-without-willing-to-cite")) {
	    print $fh $runs;
	    close $fh;
	    if($runs >= 10) {
		::status("Come on: You have run parallel $runs times. ".
			 "Isn't it about time ",
			 "you run 'parallel --citation' once to silence ".
			 "the citation notice?",
			 "");
	    }
	}
    }
}

sub status(@) {
    my @w = @_;
    my $fh = $Global::status_fd || *STDERR;
    print $fh map { ($_, "\n") } @w;
    flush $fh;
}

sub status_no_nl(@) {
    my @w = @_;
    my $fh = $Global::status_fd || *STDERR;
    print $fh @w;
    flush $fh;
}

sub warning(@) {
    my @w = @_;
    my $prog = $Global::progname || "parallel";
    status_no_nl(map { ($prog, ": Warning: ", $_, "\n"); } @w);
}

{
    my %warnings;
    sub warning_once(@) {
	my @w = @_;
	my $prog = $Global::progname || "parallel";
	$warnings{@w}++ or
	    status_no_nl(map { ($prog, ": Warning: ", $_, "\n"); } @w);
    }
}

sub error(@) {
    my @w = @_;
    my $prog = $Global::progname || "parallel";
    status(map { ($prog.": Error: ". $_); } @w);
}

sub die_bug($) {
    my $bugid = shift;
    print STDERR
	("$Global::progname: This should not happen. You have found a bug. ",
	 "Please follow\n",
	 "https://www.gnu.org/software/parallel/man.html#reporting-bugs\n",
	 "\n",
	 "Include this in the report:\n",
	 "* The version number: $Global::version\n",
	 "* The bugid: $bugid\n",
	 "* The command line being run\n",
	 "* The files being read (put the files on a webserver if they are big)\n",
	 "\n",
	 "If you get the error on smaller/fewer files, please include those instead.\n");
    ::wait_and_exit(255);
}

sub version() {
    # Returns: N/A
    print join
	("\n",
	 "GNU $Global::progname $Global::version",
	 "Copyright (C) 2007-2023 Ole Tange, http://ole.tange.dk and Free Software",
	 "Foundation, Inc.",
	 "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>",
	 "This is free software: you are free to change and redistribute it.",
	 "GNU $Global::progname comes with no warranty.",
	 "",
	 "Web site: https://www.gnu.org/software/${Global::progname}\n",
	 "When using programs that use GNU Parallel to process data for publication",
	 "please cite as described in 'parallel --citation'.\n",
	);
}

sub citation() {
    # Returns: N/A
    my ($all_argv_ref,$argv_options_removed_ref) = @_;
    my $all_argv = "@$all_argv_ref";
    my $no_opts = "@$argv_options_removed_ref";
    $all_argv=~s/--citation//;
    if($all_argv ne $no_opts) {
	::warning("--citation ignores all other options and arguments.");
	::status("");
    }

    ::status(
	"Academic tradition requires you to cite works you base your article on.",
	"If you use programs that use GNU Parallel to process data for an article in a",
	"scientific publication, please cite:",
	"",
	"\@software{tange_2023_8278274,",
	"      author       = {Tange, Ole},",
	"      title        = {GNU Parallel 20230822 ('Chandrayaan')},",
	"      month        = Aug,",
	"      year         = 2023,",
	"      note         = {{GNU Parallel is a general parallelizer to run",
	"                       multiple serial command line programs in parallel",
	"                       without changing them.}},",
	"      publisher    = {Zenodo},",
	"      doi          = {10.5281/zenodo.8278274},",
	"      url          = {https://doi.org/10.5281/zenodo.8278274}",
	"}",
	"",
	"(Feel free to use \\nocite{tange_2023_8278274})",
	"",
	# Before changing these lines, please read
	# https://www.gnu.org/software/parallel/parallel_design.html#citation-notice and
	# https://git.savannah.gnu.org/cgit/parallel.git/tree/doc/citation-notice-faq.txt
	# You accept to be put in a public hall of shame by removing
	# these lines
	"This helps funding further development; AND IT WON'T COST YOU A CENT.",
	"If you pay 10000 EUR you should feel free to use GNU Parallel without citing.",
	"",
	"More about funding GNU Parallel and the citation notice:",
	"https://lists.gnu.org/archive/html/parallel/2013-11/msg00006.html",
	"https://www.gnu.org/software/parallel/parallel_design.html#citation-notice",
	"https://git.savannah.gnu.org/cgit/parallel.git/tree/doc/citation-notice-faq.txt",
	""
	);
    while(not grep { -e "$_/will-cite" } @Global::config_dirs) {
	print "\nType: 'will cite' and press enter.\n> ";
	my $input = <STDIN>;
	if(not defined $input) {
	    exit(255);
	}
	if($input =~ /will cite/i) {
	    if(mkdir $Global::config_dir) {
                # Recompute @Global::config_dirs so we can break out of the loop.
                init_globals();
            }
	    if(open (my $fh, ">", $Global::config_dir."/will-cite")) {
		close $fh;
		::status(
		    "",
		    "Thank you for your support: You are the reason why there is funding to",
		    "continue maintaining GNU Parallel. On behalf of future versions of",
		    "GNU Parallel, which would not exist without your support:",
		    "",
		    "  THANK YOU SO MUCH",
		    "",
		    "It is really appreciated. The citation notice is now silenced.",
		    "");
	    } else {
		::status(
		      "",
		      "Thank you for your support. It is much appreciated. The citation",
		      "cannot permanently be silenced. Use '--will-cite' instead.",
		      "",
		      "If you use '--will-cite' in scripts to be run by others you are making",
		      "it harder for others to see the citation notice.  The development of",
		      "GNU Parallel is indirectly financed through citations, so if users",
		      "do not know they should cite then you are making it harder to finance",
		      "development. However, if you pay 10000 EUR, you should feel free to",
		      "use '--will-cite' in scripts.",
		      "");
		last;
	    }
	}
    }
}

sub show_limits() {
    # Returns: N/A
    print("Maximal size of command: ",Limits::Command::real_max_length(),"\n",
	  "Maximal usable size of command: ",
	  $Global::usable_command_line_length,"\n",
	  "\n",
	  "Execution will continue now, ",
	  "and it will try to read its input\n",
	  "and run commands; if this is not ",
	  "what you wanted to happen, please\n",
	  "press CTRL-D or CTRL-C\n");
}

sub embed() {
    # Give an embeddable version of GNU	 Parallel
    # Tested with: bash, zsh, ksh, ash, dash, sh
    my $randomstring = "cut-here-".join"",
	map { (0..9,"a".."z","A".."Z")[rand(62)] } (1..20);
    if(not -f $0 or not -r $0) {
	::error("--embed only works if parallel is a readable file");
	exit(255);
    }
    if(open(my $fh, "<", $0)) {
	# Read the source from $0
	my @source = <$fh>;
	my $user = $ENV{LOGNAME} || $ENV{USERNAME} || $ENV{USER};
	my @env_parallel_source = ();
	my $shell = $Global::shell;
	$shell =~ s:.*/::;
	for(which("env_parallel.$shell")) {
	    -r $_ or next;
	    # Read the source of env_parallel.shellname
	    open(my $env_parallel_source_fh, $_) || die;
	    @env_parallel_source = <$env_parallel_source_fh>;
	    close $env_parallel_source_fh;
	    last;
	}
	print "#!$Global::shell

# Copyright (C) 2007-2023 $user, Ole Tange, http://ole.tange.dk
# and Free Software Foundation, Inc.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, see <https://www.gnu.org/licenses/>
# or write to the Free Software Foundation, Inc., 51 Franklin St,
# Fifth Floor, Boston, MA 02110-1301 USA
";

	print q!
# Embedded GNU Parallel created with --embed
parallel() {
    # Start GNU	 Parallel without leaving temporary files
    #
    # Not all shells support 'perl <(cat ...)'
    # This is a complex way of doing:
    #	perl <(cat <<'cut-here'
    #	  [...]
    #	  ) "$@"
    # and also avoiding:
    #	[1]+  Done   cat

    # Make a temporary fifo that perl can read from
    _fifo_with_GNU_Parallel_source=`perl -e 'use POSIX qw(mkfifo);
      do {
	$f = "/tmp/parallel-".join"",
	  map { (0..9,"a".."z","A".."Z")[rand(62)] } (1..5);
      } while(-e $f);
      mkfifo($f,0600);
      print $f;'`
    # Put source code into temporary file
    # so it is easy to copy to the fifo
    _file_with_GNU_Parallel_source=`mktemp`;
!,
	"cat <<'$randomstring' > \$_file_with_GNU_Parallel_source\n",
	@source,
	$randomstring,"\n",
	q!
    # Copy the source code from the file to the fifo
    # and remove the file and fifo ASAP
    # 'sh -c' is needed to avoid
    #	[1]+  Done   cat
    sh -c "(rm $_file_with_GNU_Parallel_source; cat >$_fifo_with_GNU_Parallel_source; rm $_fifo_with_GNU_Parallel_source) < $_file_with_GNU_Parallel_source &"

    # Read the source from the fifo
    perl $_fifo_with_GNU_Parallel_source "$@"
}
!,
	@env_parallel_source,
	q!

# This will call the functions above
parallel -k echo ::: Put your code here
env_parallel --session
env_parallel -k echo ::: Put your code here
parset p,y,c,h -k echo ::: Put your code here
echo $p $y $c $h
echo You can also activate GNU Parallel for interactive use by:
echo . "$0"
!;
    } else {
	::error("Cannot open $0");
	exit(255);
    }
    ::status("Redirect the output to a file and add your changes at the end:",
	"  $0 --embed > new_script");
}


sub __GENERIC_COMMON_FUNCTION__() {}


sub mkdir_or_die($) {
    # If dir is not executable: die
    my $dir = shift;
    # The eval is needed to catch exception from mkdir
    eval { File::Path::mkpath($dir); };
    if(not -x $dir) {
	::error("Cannot change into non-executable dir $dir: $!");
	::wait_and_exit(255);
    }
}

sub tmpfile(@) {
    # Create tempfile as $TMPDIR/parXXXXX
    # Returns:
    #	$filehandle = opened file handle
    #	$filename = file name created
    my($filehandle,$filename) =
	::tempfile(DIR=>$ENV{'TMPDIR'}, TEMPLATE => 'parXXXXX', @_);
    if(wantarray) {
	return($filehandle,$filename);
    } else {
	# Separate unlink due to NFS dealing badly with File::Temp
	unlink $filename;
	return $filehandle;
    }
}

sub tmpname($) {
    # Select a name that does not exist
    # Do not create the file as it may be used for creating a socket (by tmux)
    # Remember the name in $Global::unlink to avoid hitting the same name twice
    my $name = shift;
    my($tmpname);
    if(not -w $ENV{'TMPDIR'}) {
	my $qtmp = ::Q($ENV{'TMPDIR'});
	if(not -e $ENV{'TMPDIR'}) {
	    ::error("Tmpdir $qtmp does not exist.","Try: mkdir -p $qtmp");
	} else {
	    ::error("Tmpdir $qtmp is not writable.","Try: chmod +w $qtmp");
	}
	::wait_and_exit(255);
    }
    do {
	$tmpname = $ENV{'TMPDIR'}."/".$name.
	    join"", map { (0..9,"a".."z","A".."Z")[rand(62)] } (1..5);
    } while(-e $tmpname or $Global::unlink{$tmpname}++);
    return $tmpname;
}

sub tmpfifo() {
    # Find an unused name and mkfifo on it
    my $tmpfifo = tmpname("fif");
    mkfifo($tmpfifo,0600);
    return $tmpfifo;
}

sub rm(@) {
    # Remove file and remove it from %Global::unlink
    # Uses:
    #	%Global::unlink
    delete @Global::unlink{@_};
    unlink @_;
}

sub size_of_block_dev() {
    # Like -s but for block devices
    # Input:
    #	$blockdev = file name of block device
    # Returns:
    #	$size = in bytes, undef if error
    my $blockdev = shift;
    if(open(my $fh, "<", $blockdev)) {
	seek($fh,0,2) || ::die_bug("cannot seek $blockdev");
	my $size = tell($fh);
	close $fh;
	return $size;
    } else {
	::error("cannot open $blockdev");
	wait_and_exit(255);
    }
}

sub qqx(@) {
    # Like qx but with clean environment (except for @keep)
    # and STDERR ignored
    # This is needed if the environment contains functions
    # that /bin/sh does not understand
    my %env;
    # ssh with ssh-agent needs PATH SSH_AUTH_SOCK SSH_AGENT_PID
    # ssh with Kerberos needs KRB5CCNAME
    # sshpass needs SSHPASS
    # tmux needs LC_CTYPE
    # lsh needs HOME LOGNAME
    my @keep = qw(PATH SSH_AUTH_SOCK SSH_AGENT_PID KRB5CCNAME LC_CTYPE
		  HOME LOGNAME SSHPASS);
    @env{@keep} = @ENV{@keep};
    local %ENV;
    %ENV = %env;
    if($Global::debug) {
	# && true is to force spawning a shell and not just exec'ing
	return qx{ @_ && true };
    } else {
	# CygWin does not respect 2>/dev/null
	# so we do that by hand
	# This trick does not work:
	# https://stackoverflow.com/q/13833088/363028
	# local *STDERR;
	# open(STDERR, ">", "/dev/null");
	open(local *CHILD_STDIN,  '<', '/dev/null') or die $!;
	open(local *CHILD_STDERR, '>', '/dev/null') or die $!;
	my $out;
	# eval is needed if open3 fails (e.g. command line too long)
	eval {
	    my $pid = open3(
		'<&CHILD_STDIN',
		$out,
		'>&CHILD_STDERR',
		# && true is to force spawning a shell and not just exec'ing
		"@_ && true");
	    my @arr = <$out>;
	    close $out;
	    # Make sure $? is set
	    waitpid($pid, 0);
	    return wantarray ? @arr : join "",@arr;
	} or do {
	    # If eval fails, force $?=false
	    `false`;
	};
    }
}

sub uniq(@) {
    # Remove duplicates and return unique values
    return keys %{{ map { $_ => 1 } @_ }};
}

sub min(@) {
    # Returns:
    #	Minimum value of array
    my $min;
    for (@_) {
	# Skip undefs
	defined $_ or next;
	defined $min or do { $min = $_; next; }; # Set $_ to the first non-undef
	$min = ($min < $_) ? $min : $_;
    }
    return $min;
}

sub max(@) {
    # Returns:
    #	Maximum value of array
    my $max;
    for (@_) {
	# Skip undefs
	defined $_ or next;
	defined $max or do { $max = $_; next; }; # Set $_ to the first non-undef
	$max = ($max > $_) ? $max : $_;
    }
    return $max;
}

sub sum(@) {
    # Returns:
    #	Sum of values of array
    my @args = @_;
    my $sum = 0;
    for (@args) {
	# Skip undefs
	$_ and do { $sum += $_; }
    }
    return $sum;
}

sub undef_as_zero($) {
    my $a = shift;
    return $a ? $a : 0;
}

sub undef_as_empty($) {
    my $a = shift;
    return $a ? $a : "";
}

sub undef_if_empty($) {
    if(defined($_[0]) and $_[0] eq "") {
	return undef;
    }
    return $_[0];
}

sub multiply_binary_prefix(@) {
    # Evalualte numbers with binary prefix
    # Ki=2^10, Mi=2^20, Gi=2^30, Ti=2^40, Pi=2^50, Ei=2^70, Zi=2^80, Yi=2^80
    # ki=2^10, mi=2^20, gi=2^30, ti=2^40, pi=2^50, ei=2^70, zi=2^80, yi=2^80
    # K =2^10, M =2^20, G =2^30, T =2^40, P =2^50, E =2^70, Z =2^80, Y =2^80
    # k =10^3, m =10^6, g =10^9, t=10^12, p=10^15, e=10^18, z=10^21, y=10^24
    # 13G = 13*1024*1024*1024 = 13958643712
    # Input:
    #	$s = string with prefixes
    # Returns:
    #	$value = int with prefixes multiplied
    my @v = @_;
    for(@v) {
	defined $_ or next;
	s/ki/*1024/gi;
	s/mi/*1024*1024/gi;
	s/gi/*1024*1024*1024/gi;
	s/ti/*1024*1024*1024*1024/gi;
	s/pi/*1024*1024*1024*1024*1024/gi;
	s/ei/*1024*1024*1024*1024*1024*1024/gi;
	s/zi/*1024*1024*1024*1024*1024*1024*1024/gi;
	s/yi/*1024*1024*1024*1024*1024*1024*1024*1024/gi;
	s/xi/*1024*1024*1024*1024*1024*1024*1024*1024*1024/gi;

	s/K/*1024/g;
	s/M/*1024*1024/g;
	s/G/*1024*1024*1024/g;
	s/T/*1024*1024*1024*1024/g;
	s/P/*1024*1024*1024*1024*1024/g;
	s/E/*1024*1024*1024*1024*1024*1024/g;
	s/Z/*1024*1024*1024*1024*1024*1024*1024/g;
	s/Y/*1024*1024*1024*1024*1024*1024*1024*1024/g;
	s/X/*1024*1024*1024*1024*1024*1024*1024*1024*1024/g;

	s/k/*1000/g;
	s/m/*1000*1000/g;
	s/g/*1000*1000*1000/g;
	s/t/*1000*1000*1000*1000/g;
	s/p/*1000*1000*1000*1000*1000/g;
	s/e/*1000*1000*1000*1000*1000*1000/g;
	s/z/*1000*1000*1000*1000*1000*1000*1000/g;
	s/y/*1000*1000*1000*1000*1000*1000*1000*1000/g;
	s/x/*1000*1000*1000*1000*1000*1000*1000*1000*1000/g;

	$_ = eval $_;
    }
    return wantarray ? @v : $v[0];
}

sub multiply_time_units($) {
    # Evalualte numbers with time units
    # s=1, m=60, h=3600, d=86400
    # Input:
    #	$s = string time units
    # Returns:
    #	$value = int in seconds
    my @v = @_;
    for(@v) {
	defined $_ or next;
	if(/[dhms]/i) {
	    s/s/*1+/gi;
	    s/m/*60+/gi;
	    s/h/*3600+/gi;
	    s/d/*86400+/gi;
	    # 1m/3 => 1*60+/3 => 1*60/3
	    s/\+(\D)/$1/gi;
	}
	$_ = eval $_."-0";
    }
    return wantarray ? @v : $v[0];
}

sub seconds_to_time_units() {
    # Convert seconds into ??d??h??m??s
    # s=1, m=60, h=3600, d=86400
    # Input:
    #	$s = int in seconds
    # Returns:
    #	$str = string time units
    my $s = shift;
    my $str;
    my $d = int($s/86400);
    $s -= $d * 86400;
    my $h = int($s/3600);
    $s -= $h * 3600;
    my $m = int($s/60);
    $s -= $m * 60;
    if($d) {
	$str = sprintf("%dd%02dh%02dm%02ds",$d,$h,$m,$s);
    } elsif($h) {
	$str = sprintf("%dh%02dm%02ds",$h,$m,$s);
    } elsif($m) {
	$str = sprintf("%dm%02ds",$m,$s);
    } else {
	$str = sprintf("%ds",$s);
    }
    return $str;
}

{
    my ($disk_full_fh, $b8193, $error_printed);
    sub exit_if_disk_full() {
	# Checks if $TMPDIR is full by writing 8kb to a tmpfile
	# If the disk is full: Exit immediately.
	# Returns:
	#   N/A
	if(not $disk_full_fh) {
	    $disk_full_fh = ::tmpfile(SUFFIX => ".df");
	    $b8193 = "b"x8193;
	}
	# Linux does not discover if a disk is full if writing <= 8192
	# Tested on:
	# bfs btrfs cramfs ext2 ext3 ext4 ext4dev jffs2 jfs minix msdos
	# ntfs reiserfs tmpfs ubifs vfat xfs
	# TODO this should be tested on different OS similar to this:
	#
	# doit() {
	#   sudo mount /dev/ram0 /mnt/loop; sudo chmod 1777 /mnt/loop
	#   seq 100000 | parallel --tmpdir /mnt/loop/ true &
	#   seq 6900000 > /mnt/loop/i && echo seq OK
	#   seq 6980868 > /mnt/loop/i
	#   seq 10000 > /mnt/loop/ii
	#   sleep 3
	#   sudo umount /mnt/loop/ || sudo umount -l /mnt/loop/
	#   echo >&2
	# }
	print $disk_full_fh $b8193;
	if(not $disk_full_fh
	   or
	   tell $disk_full_fh != 8193) {
	    # On raspbian the disk can be full except for 10 chars.
	    if(not $error_printed) {
		::error("Output is incomplete.",
			"Cannot append to buffer file in $ENV{'TMPDIR'}.",
			"Is the disk full?",
			"Change \$TMPDIR with --tmpdir or use --compress.");
		$error_printed = 1;
	    }
	    ::wait_and_exit(255);
	}
	truncate $disk_full_fh, 0;
	seek($disk_full_fh, 0, 0) || die;
    }
}

sub spacefree($$) {
    # Remove comments and spaces
    # Inputs:
    #	$spaces = keep 1 space?
    #	$s = string to remove spaces from
    # Returns:
    #	$s = with spaces removed
    my $spaces = shift;
    my $s = shift;
    $s =~ s/#.*//mg;
    if(1 == $spaces) {
	$s =~ s/\s+/ /mg;
    } elsif(2 == $spaces) {
	# Keep newlines
	$s =~ s/\n\n+/\n/sg;
	$s =~ s/[ \t]+/ /mg;
    } elsif(3 == $spaces) {
	# Keep perl code required space
	$s =~ s{([^a-zA-Z0-9/])\s+}{$1}sg;
	$s =~ s{([a-zA-Z0-9/])\s+([^:a-zA-Z0-9/])}{$1$2}sg;
    } else {
	$s =~ s/\s//mg;
    }
    return $s;
}

{
    my $hostname;
    sub hostname() {
	local $/ = "\n";
	if(not $hostname) {
	    $hostname = `hostname`;
	    chomp($hostname);
	    $hostname ||= "nohostname";
	}
	return $hostname;
    }
}

sub which(@) {
    # Input:
    #	@programs = programs to find the path to
    # Returns:
    #	@full_path = full paths to @programs. Nothing if not found
    my @which;
    for my $prg (@_) {
	push(@which, grep { not -d $_ and -x $_ }
	     map { $_."/".$prg } split(":",$ENV{'PATH'}));
	if($prg =~ m:/:) {
	    # Test if program with full path exists
	    push(@which, grep { not -d $_ and -x $_ } $prg);
	}
    }
    ::debug("which", "$which[0] in $ENV{'PATH'}\n");
    return wantarray ? @which : $which[0];
}

{
    my ($regexp,$shell,%fakename);

    sub parent_shell {
	# Input:
	#   $pid = pid to see if (grand)*parent is a shell
	# Returns:
	#   $shellpath = path to shell - undef if no shell found
	my $pid = shift;
	::debug("init","Parent of $pid\n");
	if(not $regexp) {
	    # All shells known to mankind
	    #
	    # ash bash csh dash fdsh fish fizsh ksh ksh93 mksh pdksh
	    # posh rbash rc rush rzsh sash sh static-sh tcsh yash zsh

	    my @shells = (qw(ash bash bsd-csh csh dash fdsh fish fizsh ksh
			  ksh93 lksh mksh pdksh posh rbash rc rush rzsh sash sh
			  static-sh tcsh yash zsh -sh -csh -bash),
			  '-sh (sh)' # sh on FreeBSD
		);
	    # Can be formatted as:
	    #	[sh]  -sh  sh  busybox sh  -sh (sh)
	    #	/bin/sh /sbin/sh /opt/csw/sh
	    # But not: foo.sh sshd crash flush pdflush scosh fsflush ssh
	    $shell = "(?:".join("|",map { "\Q$_\E" } @shells).")";
	    $regexp = '^((\[)(-?)('. $shell. ')(\])|(|\S+/|busybox )'.
		'(-?)('. $shell. '))( *$| [^(])';
	    %fakename = (
		# sh disguises itself as -sh (sh) on FreeBSD
		"-sh (sh)" => ["sh"],
		# csh and tcsh disguise themselves as -sh/-csh
		# E.g.: ssh -tt csh@lo 'ps aux;true' |egrep ^csh
		# but sh also disguises itself as -sh
		# (TODO When does that happen?)
		"-sh" => ["sh"],
		"-csh" => ["tcsh", "csh"],
		# ash disguises itself as -ash
		"-ash" => ["ash", "dash", "sh"],
		# dash disguises itself as -dash
		"-dash" => ["dash", "ash", "sh"],
		# bash disguises itself as -bash
		"-bash" => ["bash", "sh"],
		# ksh disguises itself as -ksh
		"-ksh" => ["ksh", "sh"],
		# zsh disguises itself as -zsh
		"-zsh" => ["zsh", "sh"],
		);
	}
	if($^O eq "linux") {
	    # Optimized for GNU/Linux
	    my $testpid = $pid;
	    my $shellpath;
	    my $shellline;
	    while($testpid) {
		if(open(my $fd, "<", "/proc/$testpid/cmdline")) {
		    local $/="\0";
		    chomp($shellline = <$fd>);
		    if($shellline =~ /$regexp/o) {
			my $shellname = $4 || $8;
			my $dash = $3 || $7;
			if($shellname eq "sh" and $dash) {
			    # -sh => csh or sh
			    if($shellpath = readlink "/proc/$testpid/exe") {
				::debug("init","procpath $shellpath\n");
				if($shellpath =~ m:/$shell$:o) {
				    ::debug("init",
					    "proc which ".$shellpath." => ");
				    return $shellpath;
				}
			    }
			}
			::debug("init", "which ".$shellname." => ");
			$shellpath = (which($shellname,
					    @{$fakename{$shellname}}))[0];
			::debug("init", "shell path $shellpath\n");
			return $shellpath;
		    }
		}
		# Get parent pid
		if(open(my $fd, "<", "/proc/$testpid/stat")) {
		    my $line = <$fd>;
		    close $fd;
		    # Parent pid is field 4
		    $testpid = (split /\s+/, $line)[3];
		} else {
		    # Something is wrong: fall back to old method
		    last;
		}
	    }
	}
	# if -sh or -csh try readlink /proc/$$/exe
	my ($children_of_ref, $parent_of_ref, $name_of_ref) = pid_table();
	my $shellpath;
	my $testpid = $pid;
	while($testpid) {
	    if($name_of_ref->{$testpid} =~ /$regexp/o) {
		my $shellname = $4 || $8;
		my $dash = $3 || $7;
		if($shellname eq "sh" and $dash) {
		    # -sh => csh or sh
		    if($shellpath = readlink "/proc/$testpid/exe") {
			::debug("init","procpath $shellpath\n");
			if($shellpath =~ m:/$shell$:o) {
			    ::debug("init", "proc which ".$shellpath." => ");
			    return $shellpath;
			}
		    }
		}
		::debug("init", "which ".$shellname." => ");
		$shellpath = (which($shellname,@{$fakename{$shellname}}))[0];
		::debug("init", "shell path $shellpath\n");
		$shellpath and last;
	    }
	    if($testpid == $parent_of_ref->{$testpid}) {
		# In Solaris zones, the PPID of the zsched process is itself
		last;
	    }
	    $testpid = $parent_of_ref->{$testpid};
	}
	return $shellpath;
    }
}

{
    my %pid_parentpid_cmd;

    sub pid_table() {
	# Returns:
	#   %children_of = { pid -> children of pid }
	#   %parent_of = { pid -> pid of parent }
	#   %name_of = { pid -> commandname }

	if(not %pid_parentpid_cmd) {
	    # Filter for SysV-style `ps`
	    my $sysv = q( ps -ef |).
		q(perl -ane '1..1 and /^(.*)CO?MM?A?N?D/ and $s=length $1;).
		q(s/^.{$s}//; print "@F[1,2] $_"' );
	    # Minix uses cols 2,3 and can have newlines in the command
	    # so lines not having numbers in cols 2,3 must be ignored
	    my $minix = q( ps -ef |).
		q(perl -ane '1..1 and /^(.*)CO?MM?A?N?D/ and $s=length $1;).
		q(s/^.{$s}// and $F[2]>0 and $F[3]>0 and print "@F[2,3] $_"' );
	    # BSD-style `ps`
	    my $bsd = q(ps -o pid,ppid,command -ax);
	    %pid_parentpid_cmd =
	    (
	     'aix' => $sysv,
	     'android' => $sysv,
	     'cygwin' => $sysv,
	     'darwin' => $bsd,
	     'dec_osf' => $sysv,
	     'dragonfly' => $bsd,
	     'freebsd' => $bsd,
	     'gnu' => $sysv,
	     'hpux' => $sysv,
	     'linux' => $sysv,
	     'mirbsd' => $bsd,
	     'minix' => $minix,
	     'msys' => $sysv,
	     'MSWin32' => $sysv,
	     'netbsd' => $bsd,
	     'nto' => $sysv,
	     'openbsd' => $bsd,
	     'solaris' => $sysv,
	     'svr5' => $sysv,
	     'syllable' => "echo ps not supported",
	    );
	}
	$pid_parentpid_cmd{$^O} or
	    ::die_bug("pid_parentpid_cmd for $^O missing");

	my (@pidtable,%parent_of,%children_of,%name_of);
	# Table with pid -> children of pid
	@pidtable = `$pid_parentpid_cmd{$^O}`;
	my $p=$$;
	for (@pidtable) {
	    # must match: 24436 21224 busybox ash
	    # must match: 24436 21224 <<empty on MacOSX running cubase>>
	    # must match: 24436 21224 <<empty on system running Viber>>
	    #	or: perl -e 'while($0=" "){}'
	    if(/^\s*(\S+)\s+(\S+)\s+(\S+.*)/
	       or
	       /^\s*(\S+)\s+(\S+)\s+()$/) {
		$parent_of{$1} = $2;
		push @{$children_of{$2}}, $1;
		$name_of{$1} = $3;
	    } else {
		::die_bug("pidtable format: $_");
	    }
	}
	return(\%children_of, \%parent_of, \%name_of);
    }
}

sub now() {
    # Returns time since epoch as in seconds with 3 decimals
    # Uses:
    #	@Global::use
    # Returns:
    #	$time = time now with millisecond accuracy
    if(not $Global::use{"Time::HiRes"}) {
	if(eval "use Time::HiRes qw ( time );") {
	    eval "sub TimeHiRestime { return Time::HiRes::time };";
	} else {
	    eval "sub TimeHiRestime { return time() };";
	}
	$Global::use{"Time::HiRes"} = 1;
    }

    return (int(TimeHiRestime()*1000))/1000;
}

sub usleep($) {
    # Sleep this many milliseconds.
    # Input:
    #	$ms = milliseconds to sleep
    my $ms = shift;
    ::debug("timing",int($ms),"ms ");
    select(undef, undef, undef, $ms/1000);
}

sub make_regexp_ungreedy {
    my $regexp = shift;
    my $class_state = 0;
    my $escape_state = 0;
    my $found = 0;
    my $ungreedy = "";
    my $c;

    for $c (split (//, $regexp)) {
	if ($found) {
	    if($c ne "?") { $ungreedy .= "?"; }
	    $found = 0;
	}
	$ungreedy .= $c;

	if ($escape_state) { $escape_state = 0; next; }
	if ($c eq "\\") { $escape_state = 1; next; }
	if ($c eq '[') { $class_state  = 1; next; }
	if ($class_state) {
	    if($c eq ']') { $class_state = 0; }
	    next;
	}
	# Quantifiers: + * {...}
	if ($c =~ /[*}+]/) { $found = 1; }
    }
    if($found) { $ungreedy .= '?'; }
    return $ungreedy;
}


sub __KILLER_REAPER__() {}

sub reap_usleep() {
    # Reap dead children.
    # If no dead children: Sleep specified amount with exponential backoff
    # Input:
    #	$ms = milliseconds to sleep
    # Returns:
    #	$ms/2+0.001 if children reaped
    #	$ms*1.1 if no children reaped
    my $ms = shift;
    if(reapers()) {
	if(not $Global::total_completed % 100) {
	    if($opt::timeout) {
		# Force cleaning the timeout queue for every 100 jobs
		# Fixes potential memleak
		$Global::timeoutq->process_timeouts();
	    }
	}
	# Sleep exponentially shorter (1/2^n) if a job finished
	return $ms/2+0.001;
    } else {
	if($opt::timeout) {
	    $Global::timeoutq->process_timeouts();
	}
	if($opt::memfree) {
	    kill_youngster_if_not_enough_mem($opt::memfree*0.5);
	}
	if($opt::memsuspend) {
	    suspend_young_if_not_enough_mem($opt::memsuspend);
	}
	if($opt::limit) {
	    kill_youngest_if_over_limit();
	}
	exit_if_disk_full();
	if($Global::linebuffer) {
	    my $something_printed = 0;
	    if($opt::keeporder and not $opt::latestline) {
		for my $job (values %Global::running) {
		    $something_printed += $job->print_earlier_jobs();
		}
	    } else {
		for my $job (values %Global::running) {
		    $something_printed += $job->print();
		}
	    }
	    if($something_printed) { $ms = $ms/2+0.001; }
	}
	if($ms > 0.002) {
	    # When a child dies, wake up from sleep (or select(,,,))
	    $SIG{CHLD} = sub { kill "ALRM", $$ };
	    if($opt::delay and not $Global::linebuffer) {
		# The 0.004s is approximately the time it takes for one round
		my $next_earliest_start =
		    $Global::newest_starttime + $opt::delay - 0.004;
		my $remaining_ms = 1000 * ($next_earliest_start - ::now());
		# The next job can only start at $next_earliest_start
		# so sleep until then (but sleep at least $ms)
		usleep(::max($ms,$remaining_ms));
	    } else {
		usleep($ms);
	    }
	    # --compress needs $SIG{CHLD} unset
	    $SIG{CHLD} = 'DEFAULT';
	}
	# Sleep exponentially longer (1.1^n) if a job did not finish,
	# though at most 1000 ms.
	return (($ms < 1000) ? ($ms * 1.1) : ($ms));
    }
}

sub kill_youngest_if_over_limit() {
    # Check each $sshlogin we are over limit
    # If over limit: kill off the youngest child
    # Put the child back in the queue.
    # Uses:
    #	%Global::running
    my %jobs_of;
    my @sshlogins;

    for my $job (values %Global::running) {
	if(not $jobs_of{$job->sshlogin()}) {
	    push @sshlogins, $job->sshlogin();
	}
	push @{$jobs_of{$job->sshlogin()}}, $job;
    }
    for my $sshlogin (@sshlogins) {
	for my $job (sort { $b->seq() <=> $a->seq() }
		     @{$jobs_of{$sshlogin}}) {
	    if($sshlogin->limit() == 2) {
		$job->kill();
		last;
	    }
	}
    }
}

sub suspend_young_if_not_enough_mem() {
    # Check each $sshlogin if there is enough mem.
    # If less than $limit free mem: suspend some of the young children
    # Else: Resume all jobs
    # Uses:
    #	%Global::running
    my $limit = shift;
    my %jobs_of;
    my @sshlogins;

    for my $job (values %Global::running) {
	if(not $jobs_of{$job->sshlogin()}) {
	    push @sshlogins, $job->sshlogin();
	}
	push @{$jobs_of{$job->sshlogin()}}, $job;
    }
    for my $sshlogin (@sshlogins) {
	my $free = $sshlogin->memfree();
	if($free < 2*$limit) {
	    # Suspend all jobs (resume some of them later)
	    map { $_->suspended() or $_->suspend(); } @{$jobs_of{$sshlogin}};
	    my @jobs = (sort { $b->seq() <=> $a->seq() }
			@{$jobs_of{$sshlogin}});
	    # how many should be running?
	    # limit*1 => 1;
	    # limit*1.5 => 2;
	    # limit*1.75 => 4;
	    # free < limit*(2-1/2^n);
	    # =>
	    # 1/(2-free/limit) < 2^n;
	    my $run = int(1/(2-$free/$limit));
	    $run = ::min($run,$#jobs);
	    # Resume the oldest running
	    for my $job ((sort { $a->seq() <=> $b->seq() } @jobs)[0..$run]) {
		::debug("mem","\nResume ",$run+1, " jobs. Seq ",
			$job->seq(), " resumed ",
			$sshlogin->memfree()," < ",2*$limit);
		$job->resume();
	    }
	} else {
	    for my $job (@{$jobs_of{$sshlogin}}) {
		if($job->suspended()) {
		    $job->resume();
		    ::debug("mem","\nResume ",$#{$jobs_of{$sshlogin}}+1,
			    " jobs. Seq ", $job->seq(), " resumed ",
			    $sshlogin->memfree()," > ",2*$limit);
		    last;
		}
	    }
	}
    }
}

sub kill_youngster_if_not_enough_mem() {
    # Check each $sshlogin if there is enough mem.
    # If less than 50% enough free mem: kill off the youngest child
    # Put the child back in the queue.
    # Uses:
    #	%Global::running
    my $limit = shift;
    my %jobs_of;
    my @sshlogins;

    for my $job (values %Global::running) {
	if(not $jobs_of{$job->sshlogin()}) {
	    push @sshlogins, $job->sshlogin();
	}
	push @{$jobs_of{$job->sshlogin()}}, $job;
    }
    for my $sshlogin (@sshlogins) {
	for my $job (sort { $b->seq() <=> $a->seq() }
		     @{$jobs_of{$sshlogin}}) {
	    if($sshlogin->memfree() < $limit) {
		::debug("mem","\n",map { $_->seq()." " }
			(sort { $b->seq() <=> $a->seq() }
			 @{$jobs_of{$sshlogin}}));
		::debug("mem","\n", $job->seq(), "killed ",
			$sshlogin->memfree()," < ",$limit);
		$job->kill();
		$sshlogin->memfree_recompute();
	    } else {
		last;
	    }
	}
	::debug("mem","Free mem OK? ",
		$sshlogin->memfree()," > ",$limit);
    }
}


sub __DEBUGGING__() {}


sub debug(@) {
    # Uses:
    #	$Global::debug
    #	%Global::fh
    # Returns: N/A
    $Global::debug or return;
    @_ = grep { defined $_ ? $_ : "" } @_;
    if($Global::debug eq "all" or $Global::debug eq $_[0]) {
	if($Global::fh{2}) {
	    # Original stderr was saved
	    my $stderr = $Global::fh{2};
	    print $stderr @_[1..$#_];
	} else {
	    print STDERR @_[1..$#_];
	}
    }
}

sub my_memory_usage() {
    # Returns:
    #	memory usage if found
    #	0 otherwise
    use strict;
    use FileHandle;

    local $/ = "\n";
    my $pid = $$;
    if(-e "/proc/$pid/stat") {
	my $fh = FileHandle->new("</proc/$pid/stat");

	my $data = <$fh>;
	chomp $data;
	$fh->close;

	my @procinfo = split(/\s+/,$data);

	return undef_as_zero($procinfo[22]);
    } else {
	return 0;
    }
}

sub my_size() {
    # Returns:
    #	$size = size of object if Devel::Size is installed
    #	-1 otherwise
    my @size_this = (@_);
    eval "use Devel::Size qw(size total_size)";
    if ($@) {
	return -1;
    } else {
	return total_size(@_);
    }
}

sub my_dump(@) {
    # Returns:
    #	ascii expression of object if Data::Dump(er) is installed
    #	error code otherwise
    my @dump_this = (@_);
    eval "use Data::Dump qw(dump);";
    if ($@) {
	# Data::Dump not installed
	eval "use Data::Dumper;";
	if ($@) {
	    my $err =  "Neither Data::Dump nor Data::Dumper is installed\n".
		"Not dumping output\n";
	    ::status($err);
	    return $err;
	} else {
	    return Dumper(@dump_this);
	}
    } else {
	# Create a dummy Data::Dump:dump as Hans Schou sometimes has
	# it undefined
	eval "sub Data::Dump:dump {}";
	eval "use Data::Dump qw(dump);";
	return (Data::Dump::dump(@dump_this));
    }
}

sub my_croak(@) {
    eval "use Carp; 1";
    $Carp::Verbose = 1;
    croak(@_);
}

sub my_carp() {
    eval "use Carp; 1";
    $Carp::Verbose = 1;
    carp(@_);
}


sub __OBJECT_ORIENTED_PARTS__() {}


package SSHLogin;

sub new($$) {
    my $class = shift;
    my $s = shift;
    my $origs = $s;
    my %hostgroups;
    my $ncpus;
    my $sshcommand;
    my $user;
    my $password;
    my $host;
    my $port;
    my $local;
    my $string;
    # SSHLogins can have these formats:
    #	@grp+grp/ncpu//usr/bin/ssh user@server
    #	ncpu//usr/bin/ssh user@server
    #	/usr/bin/ssh user@server
    #	user@server
    #	ncpu/user@server
    #	@grp+grp/user@server
    #	above with: user:password@server
    #	above with: user@server:port
    # So:
    #	[@grp+grp][ncpu/][ssh command ][[user][:password]@][server[:port]]

    #	[@grp+grp]/ncpu//usr/bin/ssh user:pass@server:port
    if($s =~ s:^\@([^/]+)/?::) {
	# Look for SSHLogin hostgroups
	%hostgroups = map { $_ => 1 } split(/\+|,/, $1);
    }
    # An SSHLogin is always in the hostgroup of its "numcpu/host"
    $hostgroups{$s} = 1;

    #	[ncpu/]/usr/bin/ssh user:pass@server:port
    if ($s =~ s:^(\d+)/::) { $ncpus = $1; }

    #	[/usr/bin/ssh ]user:pass@server:port
    if($s =~ s/^(.*) //) { $sshcommand = $1; }

    #	[user:pass@]server:port
    if($s =~ s/^([^@]+)@//) {
	my $userpw = $1;
	# user[:pass]
	if($userpw =~ s/:(.*)//) {
	    $password = $1;
	    if($password eq "") { $password = $ENV{'SSHPASS'} }
	    if(not ::which("sshpass")) {
		::error("--sshlogin with password requires sshpass installed");
		::wait_and_exit(255);
	    }
	}
	$user = $userpw;
    }
    #	[server]:port
    if(not $s =~ /:.*:/
       and
       $s =~ s/^([-a-z0-9._]+)//i) {
	# Not IPv6 (IPv6 has 2 or more ':')
	$host = $1;
    } elsif($s =~ s/^(\\[\[\]box0-9a-f.]+)//i) {
	# RFC2673 allows for:
	#   \[b11010000011101] \[o64072/14] \[xd074/14] \[208.116.0.0/14]
	$host = $1;
    } elsif($s =~ s/^\[([0-9a-f:]+)\]//i
	    or
	    $s =~ s/^([0-9a-f:]+)//i) {
	# RFC5952
	#   [2001:db8::1]:80
	#   2001:db8::1.80
	#   2001:db8::1p80
	#   2001:db8::1#80
	#   2001:db8::1:80 - not supported
	#   2001:db8::1 port 80 - not supported
	$host = $1;
    }

    #	[:port]
    if($s =~ s/^:(\w+)//i) {
	$port = $1;
    } elsif($s =~ s/^[p\.\#](\w+)//i) {
	# RFC5952
	#   2001:db8::1.80
	#   2001:db8::1p80
	#   2001:db8::1#80
	$port = $1;
    }

    if($s and $s ne ':') {
	::die_bug("SSHLogin parser failed on '$origs' => '$s'");
    }

    $string =
	# Only include the sshcommand in $string if it is set by user
	($sshcommand && $sshcommand." ").
	($user && $user."@").
	($host && $host).
	($port && ":$port");
    if($host eq ':') {
	$local = 1;
	$string = ":";
    } else {
	$sshcommand ||= $opt::ssh || $ENV{'PARALLEL_SSH'} || "ssh";
    }
    # An SSHLogin is always in the hostgroup of its $string-name
    $hostgroups{$string} = 1;
    @Global::hostgroups{keys %hostgroups} = values %hostgroups;
    # Used for file names for loadavg
    my $no_slash_string = $string;
    $no_slash_string =~ s/[^-a-z0-9:]/_/gi;
    return bless {
	'string' => $string,
	    'jobs_running' => 0,
	    'jobs_completed' => 0,
	    'maxlength' => undef,
	    'max_jobs_running' => undef,
	    'orig_max_jobs_running' => undef,
	    'ncpus' => $ncpus,
	    'sshcommand' => $sshcommand,
	    'user' => $user,
	    'password' => $password,
	    'host' => $host,
	    'port' => $port,
	    'hostgroups' => \%hostgroups,
	    'local' => $local,
	    'control_path_dir' => undef,
	    'control_path' => undef,
	    'time_to_login' => undef,
	    'last_login_at' => undef,
	    'loadavg_file' => $Global::cache_dir . "/tmp/sshlogin/" .
	    $no_slash_string . "/loadavg",
	    'loadavg' => undef,
	    'last_loadavg_update' => 0,
	    'swap_activity_file' => $Global::cache_dir . "/tmp/sshlogin/" .
	    $no_slash_string . "/swap_activity",
	    'swap_activity' => undef,
    }, ref($class) || $class;
}

sub DESTROY($) {
    my $self = shift;
    # Remove temporary files if they are created.
    ::rm($self->{'loadavg_file'});
    ::rm($self->{'swap_activity_file'});
}

sub string($) {
    my $self = shift;
    return $self->{'string'};
}

sub host($) {
    my $self = shift;
    return $self->{'host'};
}

sub sshcmd($) {
    # Give the ssh command without hostname
    # Returns:
    #	"sshpass -e ssh -p port -l user"
    my $self = shift;
    my @local;
    # [sshpass -e] ssh -p port -l user
    if($self->{'password'}) { push @local, "sshpass -e"; }
    # [ssh] -p port -l user
    # TODO sshpass + space
    push @local, $self->{'sshcommand'};
    # [-p port] -l user
    if($self->{'port'}) { push @local, '-p',$self->{'port'}; }
    # [-l user]
    if($self->{'user'}) { push @local, '-l',$self->{'user'}; }
    if($opt::controlmaster) {
	# Use control_path to make ssh faster
	my $control_path = $self->control_path_dir()."/ssh-%r@%h:%p";

	if(not $self->{'control_path'}{$control_path}++) {
	    # Master is not running for this control_path
	    # Start it
	    my $pid = fork();
	    if($pid) {
		$Global::sshmaster{$pid} ||= 1;
	    } else {
		push @local, "-S", $control_path;
		$SIG{'TERM'} = undef;
		# Run a sleep that outputs data, so it will discover
		# if the ssh connection closes.
		my $sleep = ::Q('$|=1;while(1){sleep 1;print "foo\n"}');
		# Ignore the 'foo' being printed
		open(STDOUT,">","/dev/null");
		# STDERR >/dev/null to ignore
		open(STDERR,">","/dev/null");
		open(STDIN,"<","/dev/null");
		exec(@local, "-MT", $self->{'host'}, "--",
		     "perl", "-e", $sleep);
	    }
	}
	push @local, "-S", ::Q($control_path);
    }

    return "@local";
}

sub wrap($@) {
    # Input:
    #	@cmd = shell command to run on remote
    # Returns:
    #	$sshwrapped = ssh remote @cmd
    my $self = shift;
    my @remote = @_;
    return(join " ",
	   $self->sshcmd(), $self->{'host'}, "--", "exec", @remote);
}

sub hexwrap($@) {
    # Input:
    #	@cmd = perl expresion to eval
    # Returns:
    #	$hexencoded = perl command that decodes hex and evals @cmd
    my $self = shift;
    my $cmd = join("",@_);

    # "#" is needed because Perl on MacOS X adds NULs
    # when running pack q/H10000000/
    my $hex = unpack "H*", $cmd."#";
    # csh does not deal well with > 1000 chars in one word
    # Insert space every 1000 char
    $hex =~ s/\G.{1000}\K/ /sg;
    # Explanation:
    # Write this without special chars: eval pack 'H*', join '',@ARGV
    # GNU_Parallel_worker = String so people can see this is from GNU Parallel
    # eval+	     = way to write 'eval ' without space (gives warning)
    # pack+	     = way to write 'pack ' without space
    # q/H10000000/,  = almost the same as "H*" but does not use *
    # join+q//,	     = join '',
    return('perl -X -e '.
	   'GNU_Parallel_worker,eval+pack+q/H10000000/,join+q//,@ARGV '.
	   $hex);
}

sub jobs_running($) {
    my $self = shift;
    return ($self->{'jobs_running'} || "0");
}

sub inc_jobs_running($) {
    my $self = shift;
    $self->{'jobs_running'}++;
}

sub dec_jobs_running($) {
    my $self = shift;
    $self->{'jobs_running'}--;
}

sub set_maxlength($$) {
    my $self = shift;
    $self->{'maxlength'} = shift;
}

sub maxlength($) {
    my $self = shift;
    return $self->{'maxlength'};
}

sub jobs_completed() {
    my $self = shift;
    return $self->{'jobs_completed'};
}

sub in_hostgroups() {
    # Input:
    #	@hostgroups = the hostgroups to look for
    # Returns:
    #	true if intersection of @hostgroups and the hostgroups of this
    #	     SSHLogin is non-empty
    my $self = shift;
    return grep { defined $self->{'hostgroups'}{$_} } @_;
}

sub hostgroups() {
    my $self = shift;
    return keys %{$self->{'hostgroups'}};
}

sub inc_jobs_completed($) {
    my $self = shift;
    $self->{'jobs_completed'}++;
    $Global::total_completed++;
}

sub set_max_jobs_running($$) {
    my $self = shift;
    if(defined $self->{'max_jobs_running'}) {
	$Global::max_jobs_running -= $self->{'max_jobs_running'};
    }
    $self->{'max_jobs_running'} = shift;

    if(defined $self->{'max_jobs_running'}) {
	# max_jobs_running could be resat if -j is a changed file
	$Global::max_jobs_running += $self->{'max_jobs_running'};
    }
    # Initialize orig to the first non-zero value that comes around
    $self->{'orig_max_jobs_running'} ||= $self->{'max_jobs_running'};
}

sub memfree() {
    # Returns:
    #	$memfree in bytes
    my $self = shift;
    $self->memfree_recompute();
    # Return 1 if not defined.
    return (not defined $self->{'memfree'} or $self->{'memfree'})
}

sub memfree_recompute() {
    my $self = shift;
    my $script = memfreescript();

    # TODO add sshlogin and backgrounding
    # Run the script twice if it gives 0 (typically intermittent error)
    $self->{'memfree'} = ::qqx($script) || ::qqx($script);
    if(not $self->{'memfree'}) {
	::die_bug("Less than 1 byte memory free");
    }
    #::debug("mem","New free:",$self->{'memfree'}," ");
}

{
    my $script;

    sub memfreescript() {
	# Returns:
	#   shellscript for giving available memory in bytes
	if(not $script) {
	    my %script_of = (
		# /proc/meminfo
		# MemFree:	    7012 kB
		# Buffers:	   19876 kB
		# Cached:	  431192 kB
		# SwapCached:	       0 kB
		"linux" => (
		    q{
			print 1024 * qx{
			awk '/^((Swap)?Cached|MemFree|Buffers):/
			{ sum += \$2} END { print sum }'
			    /proc/meminfo }
		    }),
		# Android uses same code as GNU/Linux
		"android" => (
		    q{
			print 1024 * qx{
			awk '/^((Swap)?Cached|MemFree|Buffers):/
			{ sum += \$2} END { print sum }'
			    /proc/meminfo }
		    }),
		# $ vmstat 1 1
		#   procs	  memory	 page			faults	     cpu
		# r  b	w    avm    free re at	pi po  fr de  sr   in	sy  cs	us sy id
		# 1  0	0 242793  389737  5  1	 0  0	0  0   0  107  978  60	 1  1 99
		"hpux" => (
		    q{
			print (((reverse `vmstat 1 1`)[0]
			    =~ /(?:\d+\D+){4}(\d+)/)[0]*1024)
		    }),
		# $ vmstat 1 2
		# kthr	    memory	      page	      disk	    faults	cpu
		# r b w	  swap	free  re  mf pi po fr de sr s3 s4 -- --	  in   sy   cs us sy id
		# 0 0 0 6496720 5170320 68 260 8 2  1  0  0 -0	3  0  0	 309 1371  255	1  2 97
		# 0 0 0 6434088 5072656	 7  15 8 0  0  0  0  0 261 0  0 1889 1899 3222	0  8 92
		#
		# The second free value is correct
		"solaris" => (
		    q{
			print (((reverse `vmstat 1 2`)[0]
				=~ /(?:\d+\D+){4}(\d+)/)[0]*1024)
		    }),
		# hw.pagesize: 4096
		# vm.stats.vm.v_cache_count: 0
		# vm.stats.vm.v_inactive_count: 79574
		# vm.stats.vm.v_free_count: 4507
		"freebsd" => (
		    q{
			for(qx{/sbin/sysctl -a}) {
			    if (/^([^:]+):\s+(.+)\s*$/s) {
				$sysctl->{$1} = $2;
			    }
			}
			print $sysctl->{"hw.pagesize"} *
			    ($sysctl->{"vm.stats.vm.v_cache_count"}
			     + $sysctl->{"vm.stats.vm.v_inactive_count"}
			     + $sysctl->{"vm.stats.vm.v_free_count"});
		    }),
		# Mach Virtual Memory Statistics: (page size of 4096 bytes)
		# Pages free:			      198061.
		# Pages active:			      159701.
		# Pages inactive:		       47378.
		# Pages speculative:		       29707.
		# Pages wired down:		       89231.
		# "Translation faults":		   928901425.
		# Pages copy-on-write:		   156988239.
		# Pages zero filled:		   271267894.
		# Pages reactivated:		       48895.
		# Pageins:			     1798068.
		# Pageouts:				 257.
		# Object cache: 6603 hits of 1713223 lookups (0% hit rate)
		'darwin' => (
		    q{
			$vm = `vm_stat`;
			print (($vm =~ /page size of (\d+)/)[0] *
			       (($vm =~ /Pages free:\s+(\d+)/)[0] +
				($vm =~ /Pages inactive:\s+(\d+)/)[0]));
		    }),
		);
	    my $perlscript = "";
	    # Make a perl script that detects the OS ($^O) and runs
	    # the appropriate command
	    for my $os (keys %script_of) {
		$perlscript .= 'if($^O eq "'.$os.'") { '.$script_of{$os}.'}';
	    }
	    $script = "perl -e " . ::Q(::spacefree(1,$perlscript));
	}
	return $script;
    }
}

sub limit($) {
    # Returns:
    #  0 = Below limit. Start another job.
    #  1 = Over limit. Start no jobs.
    #  2 = Kill youngest job
    my $self = shift;

    if(not defined $self->{'limitscript'}) {
	my %limitscripts =
	    ("io" => q!
	     io() {
		 limit=$1;
		 io_file=$2;
		 # Do the measurement in the background
		 ((tmp=$(tempfile);
		 LANG=C iostat -x 1 2 > $tmp;
		 mv $tmp $io_file) </dev/null >/dev/null & );
		 perl -e '-e $ARGV[0] or exit(1);
		   for(reverse <>) {
		     /Device/ and last;
		     /(\S+)$/ and $max = $max > $1 ? $max : $1; }
		   exit ('$limit' < $max)' $io_file;
	     };
	     io %s %s
	     !,
	     "mem" => q!
	     mem() {
		 limit=$1;
		 awk '/^((Swap)?Cached|MemFree|Buffers):/{ sum += $2}
		      END {
			 if (sum*1024 < '$limit'/2) { exit 2; }
			 else { exit (sum*1024 < '$limit') }
		      }' /proc/meminfo;
	     };
	     mem %s;
	     !,
	     "load" => q!
	     load() {
		 limit=$1;
		 ps ax -o state,command |
		     grep -E '^[DOR].[^[]' |
		     wc -l |
		 perl -ne 'exit ('$limit' < $_)';
	     };
	     load %s
	     !,
	    );
	my ($cmd,@args) = split /\s+/,$opt::limit;
	if($limitscripts{$cmd}) {
	    my $tmpfile = ::tmpname("parlmt");
	    ++$Global::unlink{$tmpfile};
	    $self->{'limitscript'} =
	    ::spacefree(1, sprintf($limitscripts{$cmd},
				   ::multiply_binary_prefix(@args),$tmpfile));
	} else {
	    $self->{'limitscript'} = $opt::limit;
	}
    }

    my %env = %ENV;
    local %ENV = %env;
    $ENV{'SSHLOGIN'} = $self->string();
    system($Global::shell,"-c",$self->{'limitscript'});
    #::qqx($self->{'limitscript'});
    ::debug("limit","limit `".$self->{'limitscript'}."` result ".($?>>8)."\n");
    return $?>>8;
}


sub swapping($) {
    my $self = shift;
    my $swapping = $self->swap_activity();
    return (not defined $swapping or $swapping)
}

sub swap_activity($) {
    # If the currently known swap activity is too old:
    #	Recompute a new one in the background
    # Returns:
    #	last swap activity computed
    my $self = shift;
    # Should we update the swap_activity file?
    my $update_swap_activity_file = 0;
    # Test with (on 64 core machine):
    # seq 100 | parallel --lb -j100 'seq 1000 | parallel  --noswap -j 1 true'
    if(open(my $swap_fh, "<", $self->{'swap_activity_file'})) {
	my $swap_out = <$swap_fh>;
	close $swap_fh;
	if($swap_out =~ /^(\d+)$/) {
	    $self->{'swap_activity'} = $1;
	    ::debug("swap", "New swap_activity: ", $self->{'swap_activity'});
	}
	::debug("swap", "Last update: ", $self->{'last_swap_activity_update'});
	if(time - $self->{'last_swap_activity_update'} > 10) {
	    # last swap activity update was started 10 seconds ago
	    ::debug("swap", "Older than 10 sec: ", $self->{'swap_activity_file'});
	    $update_swap_activity_file = 1;
	}
    } else {
	::debug("swap", "No swap_activity file: ", $self->{'swap_activity_file'});
	$self->{'swap_activity'} = undef;
	$update_swap_activity_file = 1;
    }
    if($update_swap_activity_file) {
	::debug("swap", "Updating swap_activity file ", $self->{'swap_activity_file'});
	$self->{'last_swap_activity_update'} = time;
	my $dir = ::dirname($self->{'swap_activity_file'});
	-d $dir or eval { File::Path::mkpath($dir); };
	my $swap_activity;
	$swap_activity = swapactivityscript();
	if(not $self->local()) {
	    $swap_activity = $self->wrap($swap_activity);
	}
	# Run swap_activity measuring.
	# As the command can take long to run if run remote
	# save it to a tmp file before moving it to the correct file
	my $file = $self->{'swap_activity_file'};
	my ($dummy_fh, $tmpfile) = ::tmpfile(SUFFIX => ".swp");
	::debug("swap", "\n", $swap_activity, "\n");
	my $qtmp = ::Q($tmpfile);
	my $qfile = ::Q($file);
	::qqx("($swap_activity > $qtmp && mv $qtmp $qfile || rm $qtmp &)");
    }
    return $self->{'swap_activity'};
}

{
    my $script;

    sub swapactivityscript() {
	# Returns:
	#   shellscript for detecting swap activity
	#
	# arguments for vmstat are OS dependant
	# swap_in and swap_out are in different columns depending on OS
	#
	if(not $script) {
	    my %vmstat = (
		# linux: $7*$8
		# $ vmstat 1 2
		# procs -----------memory---------- ---swap-- -----io---- -system-- ----cpu----
		#  r  b	  swpd	 free	buff  cache   si   so	 bi    bo   in	 cs us sy id wa
		#  5  0	 51208 1701096 198012 18857888	  0    0    37	 153   28   19 56 11 33	 1
		#  3  0	 51208 1701288 198012 18857972	  0    0     0	   0 3638 10412 15  3 82  0
		'linux' => ['vmstat 1 2 | tail -n1', '$7*$8'],

		# solaris: $6*$7
		# $ vmstat -S 1 2
		#  kthr	     memory	       page	       disk	     faults	 cpu
		#  r b w   swap	 free  si  so pi po fr de sr s3 s4 -- --   in	sy   cs us sy id
		#  0 0 0 4628952 3208408 0  0  3  1  1	0  0 -0	 2  0  0  263  613  246	 1  2 97
		#  0 0 0 4552504 3166360 0  0  0  0  0	0  0  0	 0  0  0  246  213  240	 1  1 98
		'solaris' => ['vmstat -S 1 2 | tail -1', '$6*$7'],

		# darwin (macosx): $21*$22
		# $ vm_stat -c 2 1
		# Mach Virtual Memory Statistics: (page size of 4096 bytes)
		#     free   active   specul inactive throttle	  wired	 prgable   faults     copy    0fill reactive   purged file-backed anonymous cmprssed cmprssor  dcomprs	 comprs	 pageins  pageout  swapins swapouts
		#   346306   829050    74871   606027	     0	 240231	   90367  544858K 62343596  270837K    14178   415070	   570102    939846	 356	  370	   116	    922	 4019813	4	 0	  0
		#   345740   830383    74875   606031	     0	 239234	   90369     2696      359	553	   0	    0	   570110    941179	 356	  370	     0	      0	       0	0	 0	  0
		'darwin' => ['vm_stat -c 2 1 | tail -n1', '$21*$22'],

		# ultrix: $12*$13
		# $ vmstat -S 1 2
		#  procs      faults	cpu	 memory		     page	      disk
		#  r b w   in  sy  cs us sy id	avm  fre  si so	 pi  po	 fr  de	 sr s0
		#  1 0 0    4  23   2  3  0 97 7743 217k   0  0	  0   0	  0   0	  0  0
		#  1 0 0    6  40   8  0  1 99 7743 217k   0  0	  3   0	  0   0	  0  0
		'ultrix' => ['vmstat -S 1 2 | tail -1', '$12*$13'],

		# aix: $6*$7
		# $ vmstat 1 2
		# System configuration: lcpu=1 mem=2048MB
		#
		# kthr	  memory	      page		faults	      cpu
		# ----- ----------- ------------------------ ------------ -----------
		#  r  b	  avm	fre  re	 pi  po	 fr   sr  cy  in   sy  cs us sy id wa
		#  0  0 333933 241803	0   0	0   0	 0   0	10  143	 90  0	0 99  0
		#  0  0 334125 241569	0   0	0   0	 0   0	37 5368 184  0	9 86  5
		'aix' => ['vmstat 1 2 | tail -n1', '$6*$7'],

		# freebsd: $8*$9
		# $ vmstat -H 1 2
		#  procs      memory	  page			  disks	    faults	   cpu
		#  r b w     avm    fre	  flt  re  pi  po    fr	 sr ad0 ad1   in   sy	cs us sy id
		#  1 0 0  596716   19560    32	 0   0	 0    33   8   0   0   11  220	277  0	0 99
		#  0 0 0  596716   19560     2	 0   0	 0     0   0   0   0   11  144	263  0	1 99
		'freebsd' => ['vmstat -H 1 2 | tail -n1', '$8*$9'],

		# mirbsd: $8*$9
		# $ vmstat 1 2
		#  procs   memory	 page			 disks	   traps	 cpu
		#  r b w    avm	   fre	 flt  re  pi  po  fr  sr wd0 cd0  int	sys   cs us sy id
		#  0 0 0  25776 164968	  34   0   0   0   0   0   0   0  230	259   38  4  0 96
		#  0 0 0  25776 164968	  24   0   0   0   0   0   0   0  237	275   37  0  0 100
		'mirbsd' => ['vmstat 1 2 | tail -n1', '$8*$9'],

		# netbsd: $7*$8
		# $ vmstat 1 2
		#  procs    memory	page			   disks   faults      cpu
		#  r b	    avm	   fre	flt  re	 pi   po   fr	sr w0 w1   in	sy  cs us sy id
		#  0 0	 138452	  6012	 54   0	  0    0    1	 2  3  0    4  100  23	0  0 100
		#  0 0	 138456	  6008	  1   0	  0    0    0	 0  0  0    7	26  19	0 0 100
		'netbsd' => ['vmstat 1 2 | tail -n1', '$7*$8'],

		# openbsd: $8*$9
		# $ vmstat 1 2
		#  procs    memory	 page			 disks	  traps		 cpu
		#  r b w    avm	    fre	 flt  re  pi  po  fr  sr wd0 wd1  int	sys   cs us sy id
		#  0 0 0  76596	 109944	  73   0   0   0   0   0   0   1    5	259   22  0  1 99
		#  0 0 0  76604	 109936	  24   0   0   0   0   0   0   0    7	114   20  0  1 99
		'openbsd' => ['vmstat 1 2 | tail -n1', '$8*$9'],

		# hpux: $8*$9
		# $ vmstat 1 2
		#	   procs	   memory		    page			      faults	   cpu
		#     r	    b	  w	 avm	free   re   at	  pi   po    fr	  de	sr     in     sy    cs	us sy id
		#     1	    0	  0   247211  216476	4    1	   0	0     0	   0	 0    102  73005    54	 6 11 83
		#     1	    0	  0   247211  216421   43    9	   0	0     0	   0	 0    144   1675    96	25269512791222387000 25269512791222387000 105
		'hpux' => ['vmstat 1 2 | tail -n1', '$8*$9'],

		# dec_osf (tru64): $11*$12
		# $ vmstat  1 2
		# Virtual Memory Statistics: (pagesize = 8192)
		#   procs      memory	     pages			      intr	 cpu
		#   r	w   u  act free wire fault  cow zero react  pin pout  in  sy  cs us sy id
		#   3 181  36  51K 1895 8696  348M  59M 122M   259  79M	   0   5 218 302  4  1 94
		#   3 181  36  51K 1893 8696	 3   15	  21	 0   28	   0   4  81 321  1  1 98
		'dec_osf' => ['vmstat 1 2 | tail -n1', '$11*$12'],

		# gnu (hurd): $7*$8
		# $ vmstat -k 1 2
		# (pagesize: 4, size: 512288, swap size: 894972)
		#   free   actv	 inact	wired	zeroed	react	 pgins	 pgouts	 pfaults  cowpfs hrat	 caobj	cache swfree
		# 371940  30844	 89228	20276	298348	    0	 48192	  19016	  756105   99808  98%	   876	20628 894972
		# 371940  30844	 89228	20276	    +0	   +0	    +0	     +0	     +42      +2  98%	   876	20628 894972
		'gnu' => ['vmstat -k 1 2 | tail -n1', '$7*$8'],

		# -nto (qnx has no swap)
		#-irix
		#-svr5 (scosysv)
		);
	    my $perlscript = "";
	    # Make a perl script that detects the OS ($^O) and runs
	    # the appropriate vmstat command
	    for my $os (keys %vmstat) {
		$vmstat{$os}[1] =~ s/\$/\\\\\\\$/g; # $ => \\\$
		$perlscript .= 'if($^O eq "'.$os.'") { print `'.$vmstat{$os}[0].' | awk "{print ' .
		    $vmstat{$os}[1] . '}"` }';
	    }
	    $script = "perl -e " . ::Q($perlscript);
	}
	return $script;
    }
}

sub too_fast_remote_login($) {
    my $self = shift;
    if($self->{'last_login_at'} and $self->{'time_to_login'}) {
	# sshd normally allows 10 simultaneous logins
	# A login takes time_to_login
	# So time_to_login/5 should be safe
	# If now <= last_login + time_to_login/5: Then it is too soon.
	my $too_fast = (::now() <= $self->{'last_login_at'}
			+ $self->{'time_to_login'}/5);
	::debug("run", "Too fast? $too_fast ");
	return $too_fast;
    } else {
	# No logins so far (or time_to_login not computed): it is not too fast
	return 0;
    }
}

sub last_login_at($) {
    my $self = shift;
    return $self->{'last_login_at'};
}

sub set_last_login_at($$) {
    my $self = shift;
    $self->{'last_login_at'} = shift;
}

sub loadavg_too_high($) {
    my $self = shift;
    my $loadavg = $self->loadavg();
    if(defined $loadavg) {
	::debug("load", "Load $loadavg > ",$self->max_loadavg());
	return $loadavg >= $self->max_loadavg();
    } else {
	# Unknown load: Assume load is too high
	return 1;
    }
}



sub loadavg($) {
    # If the currently know loadavg is too old:
    #	Recompute a new one in the background
    # The load average is computed as the number of processes waiting
    # for disk or CPU right now. So it is the server load this instant
    # and not averaged over several minutes. This is needed so GNU
    # Parallel will at most start one job that will push the load over
    # the limit.
    #
    # Returns:
    #	$last_loadavg = last load average computed (undef if none)

    my $self = shift;
    sub loadavg_cmd() {
	if(not $Global::loadavg_cmd) {
	    # aix => "ps -ae -o state,command" # state wrong
	    # bsd => "ps ax -o state,command"
	    # sysv => "ps -ef -o s -o comm"
	    # cygwin => perl -ne 'close STDERR; /Name/ and print"\n"; \
	    #	 /(Name|Pid|Ppid|State):\s+(\S+)/ and print "$2\t";' /proc/*/status |
	    #	 awk '{print $2,$1}'
	    # dec_osf => bsd
	    # dragonfly => bsd
	    # freebsd => bsd
	    # gnu => bsd
	    # hpux => ps -el|awk '{print $2,$14,$15}'
	    # irix => ps -ef -o state -o comm
	    # linux => bsd
	    # minix => ps el|awk '{print \$1,\$11}'
	    # mirbsd => bsd
	    # netbsd => bsd
	    # openbsd => bsd
	    # solaris => sysv
	    # svr5 => sysv
	    # ultrix => ps -ax | awk '{print $3,$5}'
	    # unixware => ps -el|awk '{print $2,$14,$15}'
	    my $ps = ::spacefree(1,q{
		$sysv="ps -ef -o s -o comm";
		$sysv2="ps -ef -o state -o comm";
		$bsd="ps ax -o state,command";
		# Treat threads as processes
		$bsd2="ps axH -o state,command";
		$psel="ps -el|awk '{ print \$2,\$14,\$15 }'";
		$cygwin=q{ perl -ne 'close STDERR; /Name/ and print"\n";
		    /(Name|Pid|Ppid|State):\s+(\S+)/ and print "$2\t";' /proc/*/status |
		    awk '{print $2,$1}' };
		$dummy="echo S COMMAND;echo R dummy";
		%ps=(
		    # TODO Find better code for AIX/Android
		    'aix' => "uptime",
		    'android' => "uptime",
		    'cygwin' => $cygwin,
		    'darwin' => $bsd,
		    'dec_osf' => $sysv2,
		    'dragonfly' => $bsd,
		    'freebsd' => $bsd2,
		    'gnu' => $bsd,
		    'hpux' => $psel,
		    'irix' => $sysv2,
		    'linux' => $bsd2,
		    'minix' => "ps el|awk '{print \$1,\$11}'",
		    'mirbsd' => $bsd,
		    'msys' => $cygwin,
		    'netbsd' => $bsd,
		    'nto' => $dummy,
		    'openbsd' => $bsd,
		    'solaris' => $sysv,
		    'svr5' => $psel,
		    'ultrix' => "ps -ax | awk '{print \$3,\$5}'",
		    'MSWin32' => $sysv,
		    );
		print `$ps{$^O}`;
	    });
	    # The command is too long for csh, so base64_wrap the command
	    $Global::loadavg_cmd = $self->hexwrap($ps);
	}
	return $Global::loadavg_cmd;
    }
    # Should we update the loadavg file?
    my $update_loadavg_file = 0;
    if(open(my $load_fh, "<", $self->{'loadavg_file'})) {
	local $/; # $/ = undef => slurp whole file
	my $load_out = <$load_fh>;
	close $load_fh;
	if($load_out =~ /\S/) {
	    # Content can be empty if ~/ is on NFS
	    # due to reading being non-atomic.
	    #
	    # Count lines starting with D,O,R but command does not start with [
	    my $load =()= ($load_out=~/(^\s?[DOR]\S* +(?=[^\[])\S)/gm);
	    if($load > 0) {
		# load is overestimated by 1
		$self->{'loadavg'} = $load - 1;
		::debug("load", "New loadavg: ", $self->{'loadavg'},"\n");
	    } elsif ($load_out=~/average: (\d+.\d+)/) {
		# AIX does not support instant load average
		# 04:11AM   up 21 days,	 12:55,	 1 user,  load average: 1.85, 1.57, 1.55
		$self->{'loadavg'} = $1;
	    } else {
		::die_bug("loadavg_invalid_content: " .
			  $self->{'loadavg_file'} . "\n$load_out");
	    }
	}
	$update_loadavg_file = 1;
    } else {
	::debug("load", "No loadavg file: ", $self->{'loadavg_file'});
	$self->{'loadavg'} = undef;
	$update_loadavg_file = 1;
    }
    if($update_loadavg_file) {
	::debug("load", "Updating loadavg file", $self->{'loadavg_file'}, "\n");
	$self->{'last_loadavg_update'} = time;
	my $dir = ::dirname($self->{'swap_activity_file'});
	-d $dir or eval { File::Path::mkpath($dir); };
	-w $dir or ::die_bug("Cannot write to $dir");
	my $cmd = "";
	if($self->{'string'} ne ":") {
	    $cmd = $self->wrap(loadavg_cmd());
	} else {
	    $cmd .= loadavg_cmd();
	}
	# As the command can take long to run if run remote
	# save it to a tmp file before moving it to the correct file
	::debug("load", "Update load\n");
	my $file = ::Q($self->{'loadavg_file'});
	# tmpfile on same filesystem as $file
	my $tmpfile = $file.$$;
	$ENV{'SSHPASS'} = $self->{'password'};
	::qqx("($cmd > $tmpfile && mv $tmpfile $file || rm $tmpfile & )");
    }
    return $self->{'loadavg'};
}

sub max_loadavg($) {
    my $self = shift;
    # If --load is a file it might be changed
    if($Global::max_load_file) {
	my $mtime = (stat($Global::max_load_file))[9];
	if($mtime > $Global::max_load_file_last_mod) {
	    $Global::max_load_file_last_mod = $mtime;
	    for my $sshlogin (values %Global::host) {
		$sshlogin->set_max_loadavg(undef);
	    }
	}
    }
    if(not defined $self->{'max_loadavg'}) {
	$self->{'max_loadavg'} =
	    $self->compute_max_loadavg($opt::load);
    }
    ::debug("load", "max_loadavg: ", $self->string(), " ", $self->{'max_loadavg'});
    return $self->{'max_loadavg'};
}

sub set_max_loadavg($$) {
    my $self = shift;
    $self->{'max_loadavg'} = shift;
}

sub compute_max_loadavg($) {
    # Parse the max loadaverage that the user asked for using --load
    # Returns:
    #	max loadaverage
    my $self = shift;
    my $loadspec = shift;
    my $load;
    if(defined $loadspec) {
	if($loadspec =~ /^\+(\d+)$/) {
	    # E.g. --load +2
	    my $j = $1;
	    $load =
		$self->ncpus() + $j;
	} elsif ($loadspec =~ /^-(\d+)$/) {
	    # E.g. --load -2
	    my $j = $1;
	    $load =
		$self->ncpus() - $j;
	} elsif ($loadspec =~ /^(\d+)\%$/) {
	    my $j = $1;
	    $load =
		$self->ncpus() * $j / 100;
	} elsif ($loadspec =~ /^(\d+(\.\d+)?)$/) {
	    $load = $1;
	} elsif (-f $loadspec) {
	    $Global::max_load_file = $loadspec;
	    $Global::max_load_file_last_mod = (stat($Global::max_load_file))[9];
	    if(open(my $in_fh, "<", $Global::max_load_file)) {
		my $opt_load_file = join("",<$in_fh>);
		close $in_fh;
		$load = $self->compute_max_loadavg($opt_load_file);
	    } else {
		::error("Cannot open $loadspec.");
		::wait_and_exit(255);
	    }
	} else {
	    ::error("Parsing of --load failed.");
	    ::die_usage();
	}
	if($load < 0.01) {
	    $load = 0.01;
	}
    }
    return $load;
}

sub time_to_login($) {
    my $self = shift;
    return $self->{'time_to_login'};
}

sub set_time_to_login($$) {
    my $self = shift;
    $self->{'time_to_login'} = shift;
}

sub max_jobs_running($) {
    my $self = shift;
    if(not defined $self->{'max_jobs_running'}) {
	my $nproc = $self->compute_number_of_processes($opt::jobs);
	$self->set_max_jobs_running($nproc);
    }
    return $self->{'max_jobs_running'};
}

sub orig_max_jobs_running($) {
    my $self = shift;
    return $self->{'orig_max_jobs_running'};
}

sub compute_number_of_processes($) {
    # Number of processes wanted and limited by system resources
    # Returns:
    #	Number of processes
    my $self = shift;
    my $opt_P = shift;
    my $wanted_processes = $self->user_requested_processes($opt_P);
    if(not defined $wanted_processes) {
	$wanted_processes = $Global::default_simultaneous_sshlogins;
    }
    ::debug("load", "Wanted procs: $wanted_processes\n");
    my $system_limit =
	$self->processes_available_by_system_limit($wanted_processes);
    ::debug("load", "Limited to procs: $system_limit\n");
    return $system_limit;
}

{
    my @children;
    my $max_system_proc_reached;
    my $more_filehandles;
    my %fh;
    my $tmpfhname;
    my $count_jobs_already_read;
    my @jobs;
    my $job;
    my @args;
    my $arg;

    sub reserve_filehandles($) {
	# Reserves filehandle
	my $n = shift;
	for (1..$n) {
	    $more_filehandles &&= open($fh{$tmpfhname++}, "<", "/dev/null");
	}
    }

    sub reserve_process() {
	# Spawn a dummy process
	my $child;
	if($child = fork()) {
	    push @children, $child;
	    $Global::unkilled_children{$child} = 1;
	} elsif(defined $child) {
	    # This is the child
	    # The child takes one process slot
	    # It will be killed later
	    $SIG{'TERM'} = $Global::original_sig{'TERM'};
	    if($^O eq "cygwin" or $^O eq "msys" or $^O eq "nto") {
		# The exec does not work on Cygwin and QNX
		sleep 10101010;
	    } else {
		# 'exec sleep' takes less RAM than sleeping in perl
		exec 'sleep', 10101;
	    }
	    exit(0);
	} else {
	    # Failed to spawn
	    $max_system_proc_reached = 1;
	}
    }

    sub get_args_or_jobs() {
	# Get an arg or a job (depending on mode)
	if($Global::semaphore or ($opt::pipe and not $opt::tee)) {
	    # Skip: No need to get args
	    return 1;
	} elsif(defined $opt::retries and $count_jobs_already_read) {
	    # For retries we may need to run all jobs on this sshlogin
	    # so include the already read jobs for this sshlogin
	    $count_jobs_already_read--;
	    return 1;
	} else {
	    if($opt::X or $opt::m) {
		# The arguments may have to be re-spread over several jobslots
		# So pessimistically only read one arg per jobslot
		# instead of a full commandline
		if($Global::JobQueue->{'commandlinequeue'}->{'arg_queue'}->empty()) {
		    if($Global::JobQueue->empty()) {
			return 0;
		    } else {
			$job = $Global::JobQueue->get();
			push(@jobs, $job);
			return 1;
		    }
		} else {
		    $arg = $Global::JobQueue->{'commandlinequeue'}->{'arg_queue'}->get();
		    push(@args, $arg);
		    return 1;
		}
	    } else {
		# If there are no more command lines, then we have a process
		# per command line, so no need to go further
		if($Global::JobQueue->empty()) {
		    return 0;
		} else {
		    $job = $Global::JobQueue->get();
		    # Replacement must happen here due to seq()
		    $job and $job->replaced();
		    push(@jobs, $job);
		    return 1;
		}
	    }
	}
    }

    sub cleanup() {
	# Cleanup: Close the files
	for (values %fh) { close $_ }
	# Cleanup: Kill the children
	for my $pid (@children) {
	    kill 9, $pid;
	    waitpid($pid,0);
	    delete $Global::unkilled_children{$pid};
	}
	# Cleanup: Unget the command_lines or the @args
	$Global::JobQueue->{'commandlinequeue'}{'arg_queue'}->unget(@args);
	@args = ();
	$Global::JobQueue->unget(@jobs);
	@jobs = ();
    }

    sub processes_available_by_system_limit($) {
	# If the wanted number of processes is bigger than the system limits:
	# Limit them to the system limits
	# Limits are: File handles, number of input lines, processes,
	# and taking > 1 second to spawn 10 extra processes
	# Returns:
	#   Number of processes
	my $self = shift;
	my $wanted_processes = shift;
	my $system_limit = 0;
	my $slow_spawning_warning_printed = 0;
	my $time = time;
	$more_filehandles = 1;
	$tmpfhname = "TmpFhNamE";

	# perl uses 7 filehandles for something?
	# parallel uses 1 for memory_usage
	# parallel uses 4 for ?
	reserve_filehandles(12);
	# Two processes for load avg and ?
	reserve_process();
	reserve_process();

	# For --retries count also jobs already run
	$count_jobs_already_read = $Global::JobQueue->next_seq();
	my $wait_time_for_getting_args = 0;
	my $start_time = time;
	if($wanted_processes < $Global::infinity) {
	    $Global::dummy_jobs = 1;
	}
	while(1) {
	    $system_limit >= $wanted_processes and last;
	    not $more_filehandles and last;
	    $max_system_proc_reached and last;

	    my $before_getting_arg = time;
	    if(!$Global::dummy_jobs) {
		get_args_or_jobs() or last;
	    }
	    $wait_time_for_getting_args += time - $before_getting_arg;
	    $system_limit++;

	    # Every simultaneous process uses 2 filehandles to write to
	    # and 2 filehandles to read from
	    reserve_filehandles(4);

	    # System process limit
	    reserve_process();

	    my $forktime = time - $time - $wait_time_for_getting_args;
	    ::debug("run", "Time to fork $system_limit procs: ".
		    $wait_time_for_getting_args, " ", $forktime,
		    " (processes so far: ", $system_limit,")\n");
	    if($system_limit > 10 and
	       $forktime > 1 and
	       $forktime > $system_limit * 0.01) {
		# It took more than 0.01 second to fork a processes on avg.
		# Give the user a warning. He can press Ctrl-C if this
		# sucks.
		::warning_once(
		      "Starting $system_limit processes took > $forktime sec.",
		      "Consider adjusting -j. Press CTRL-C to stop.");
	    }
	}
	cleanup();

	if($system_limit < $wanted_processes) {
	    # The system_limit is less than the wanted_processes
	    if($system_limit < 1 and not $Global::JobQueue->empty()) {
		::warning("Cannot spawn any jobs.",
			  "Try increasing 'ulimit -u' (try: ulimit -u `ulimit -Hu`)",
			  "or increasing 'nproc' in /etc/security/limits.conf",
			  "or increasing /proc/sys/kernel/pid_max");
		::wait_and_exit(255);
	    }
	    if(not $more_filehandles) {
		::warning("Only enough file handles to run ".
			  $system_limit. " jobs in parallel.",
			  "Try running 'parallel -j0 -N $system_limit --pipe parallel -j0'",
			  "or increasing 'ulimit -n' (try: ulimit -n `ulimit -Hn`)",
			  "or increasing 'nofile' in /etc/security/limits.conf",
			  "or increasing /proc/sys/fs/file-max");
	    }
	    if($max_system_proc_reached) {
		::warning("Only enough available processes to run ".
			  $system_limit. " jobs in parallel.",
			  "Try increasing 'ulimit -u' (try: ulimit -u `ulimit -Hu`)",
			  "or increasing 'nproc' in /etc/security/limits.conf",
			  "or increasing /proc/sys/kernel/pid_max");
	    }
	}
	if($] == 5.008008 and $system_limit > 1000) {
	    # https://savannah.gnu.org/bugs/?36942
	    $system_limit = 1000;
	}
	if($Global::JobQueue->empty()) {
	    $system_limit ||= 1;
	}
	if($self->string() ne ":" and
	   $system_limit > $Global::default_simultaneous_sshlogins) {
	    $system_limit =
		$self->simultaneous_sshlogin_limit($system_limit);
	}
	return $system_limit;
    }
}

sub simultaneous_sshlogin_limit($) {
    # Test by logging in wanted number of times simultaneously
    # Returns:
    #	min($wanted_processes,$working_simultaneous_ssh_logins-1)
    my $self = shift;
    my $wanted_processes = shift;
    if($self->{'time_to_login'}) {
	return $wanted_processes;
    }

    # Try twice because it guesses wrong sometimes
    # Choose the minimal
    my $ssh_limit =
	::min($self->simultaneous_sshlogin($wanted_processes),
	      $self->simultaneous_sshlogin($wanted_processes));
    if($ssh_limit < $wanted_processes) {
	my $serverlogin = $self->string();
	::warning("ssh to $serverlogin only allows ".
		  "for $ssh_limit simultaneous logins.",
		  "You may raise this by changing",
		  "/etc/ssh/sshd_config:MaxStartups and MaxSessions on $serverlogin.",
		  "You can also try --sshdelay 0.1",
		  "Using only ".($ssh_limit-1)." connections ".
		  "to avoid race conditions.");
	# Race condition can cause problem if using all sshs.
	if($ssh_limit > 1) { $ssh_limit -= 1; }
    }
    return $ssh_limit;
}

sub simultaneous_sshlogin($) {
    # Using $sshlogin try to see if we can do $wanted_processes
    # simultaneous logins
    # (ssh host echo simul-login & ssh host echo simul-login & ...) |
    #	grep simul|wc -l
    # Input:
    #	$wanted_processes = Try for this many logins in parallel
    # Returns:
    #	$ssh_limit = Number of succesful parallel logins
    local $/ = "\n";
    my $self = shift;
    my $wanted_processes = shift;
    my $sshdelay = $opt::sshdelay ? "sleep $opt::sshdelay;" : "";
    # TODO sh -c wrapper to work for csh
    my $cmd = ($sshdelay.$self->wrap("echo simultaneouslogin").
	       "</dev/null 2>&1 &")x$wanted_processes;
    ::debug("init","Trying $wanted_processes logins at ".$self->string()."\n");
    open (my $simul_fh, "-|", "($cmd)|grep simultaneouslogin | wc -l") or
	::die_bug("simultaneouslogin");
    my $ssh_limit = <$simul_fh>;
    close $simul_fh;
    chomp $ssh_limit;
    return $ssh_limit;
}

sub set_ncpus($$) {
    my $self = shift;
    $self->{'ncpus'} = shift;
}

sub user_requested_processes($) {
    # Parse the number of processes that the user asked for using -j
    # Input:
    #	$opt_P = string formatted as for -P
    # Returns:
    #	$processes = the number of processes to run on this sshlogin
    my $self = shift;
    my $opt_P = shift;
    my $processes;
    if(defined $opt_P) {
	if (-f $opt_P) {
	    $Global::max_procs_file = $opt_P;
	    if(open(my $in_fh, "<", $Global::max_procs_file)) {
		my $opt_P_file = join("",<$in_fh>);
		close $in_fh;
		if($opt_P_file !~ /\S/) {
		    ::warning_once("$Global::max_procs_file is empty. ".
				   "Treated as 100%");
		    $opt_P_file = "100%";
		}
		$processes = $self->user_requested_processes($opt_P_file);
	    } else {
		::error("Cannot open $opt_P.");
		::wait_and_exit(255);
	    }
	} else {
	    if($opt_P eq "0") {
		# -P 0 = infinity (or at least close)
		$processes = $Global::infinity;
	    } else {
		# -P +3 and -P -1
		$opt_P =~ s/^([-+])/\$self->ncpus()$1/;
		# -P 40%
		$opt_P =~ s:%$:*\$self->ncpus()/100:;
		$processes = eval $opt_P;
		if($processes <= 0) {
		    # Do not go below 1
		    $processes = 1;
		}
	    }
	}
	$processes = ::ceil($processes);
    }
    return $processes;
}

sub ncpus($) {
    # Number of CPU threads
    # --use_sockets_instead_of_threads = count socket instead
    # --use_cores_instead_of_threads = count physical cores instead
    # Returns:
    #	$ncpus = number of cpu (threads) on this sshlogin
    local $/ = "\n";
    my $self = shift;
    if(not defined $self->{'ncpus'}) {
	if($self->local()) {
	    if($opt::use_sockets_instead_of_threads) {
		$self->{'ncpus'} = socket_core_thread()->{'sockets'};
	    } elsif($opt::use_cores_instead_of_threads) {
		$self->{'ncpus'} = socket_core_thread()->{'cores'};
	    } else {
		$self->{'ncpus'} = socket_core_thread()->{'threads'};
	    }
	} else {
	    my $ncpu;
	    $ENV{'SSHPASS'} = $self->{'password'};
	    ::debug("init",("echo | ".$self->wrap("parallel --number-of-sockets")));
	    if($opt::use_sockets_instead_of_threads
	       or
		$opt::use_cpus_instead_of_cores) {
		$ncpu = ::qqx("echo | ".$self->wrap("parallel --number-of-sockets"));
	    } elsif($opt::use_cores_instead_of_threads) {
		$ncpu = ::qqx("echo | ".$self->wrap("parallel --number-of-cores"));
	    } else {
		$ncpu = ::qqx("echo | ".$self->wrap("parallel --number-of-threads"));
	    }
	    chomp $ncpu;
	    if($ncpu =~ /^\s*[0-9]+\s*$/s) {
		$self->{'ncpus'} = $ncpu;
	    } else {
		::warning("Could not figure out ".
			  "number of cpus on ".$self->string." ($ncpu). Using 1.");
		$self->{'ncpus'} = 1;
	    }
	}
    }
    return $self->{'ncpus'};
}


sub nproc() {
    # Returns:
    #	Number of threads using `nproc`
    my $no_of_threads = ::qqx("nproc");
    chomp $no_of_threads;
    return $no_of_threads;
}

sub no_of_sockets() {
    return socket_core_thread()->{'sockets'};
}

sub no_of_cores() {
    return socket_core_thread()->{'cores'};
}

sub no_of_threads() {
    return socket_core_thread()->{'threads'};
}

sub socket_core_thread() {
    # Returns:
    #	{
    #	  'sockets' => #sockets = number of socket with CPU present
    #	  'cores' => #cores = number of physical cores
    #	  'threads' => #threads = number of compute cores (hyperthreading)
    #	  'active' => #taskset_threads = number of taskset limited cores
    #	}
    my $cpu;
    if ($^O eq 'linux') {
	$cpu = sct_gnu_linux($cpu);
    } elsif ($^O eq 'android') {
	$cpu = sct_android($cpu);
    } elsif ($^O eq 'freebsd') {
	$cpu = sct_freebsd($cpu);
    } elsif ($^O eq 'netbsd') {
	$cpu = sct_netbsd($cpu);
    } elsif ($^O eq 'openbsd') {
	$cpu = sct_openbsd($cpu);
    } elsif ($^O eq 'gnu') {
	$cpu = sct_hurd($cpu);
    } elsif ($^O eq 'darwin') {
	$cpu = sct_darwin($cpu);
    } elsif ($^O eq 'solaris') {
	$cpu = sct_solaris($cpu);
    } elsif ($^O eq 'aix') {
	$cpu = sct_aix($cpu);
    } elsif ($^O eq 'hpux') {
	$cpu = sct_hpux($cpu);
    } elsif ($^O eq 'nto') {
	$cpu = sct_qnx($cpu);
    } elsif ($^O eq 'svr5') {
	$cpu = sct_openserver($cpu);
    } elsif ($^O eq 'irix') {
	$cpu = sct_irix($cpu);
    } elsif ($^O eq 'dec_osf') {
	$cpu = sct_tru64($cpu);
    } else {
	# Try all methods until we find something that works
	$cpu = (sct_gnu_linux($cpu)
		|| sct_android($cpu)
		|| sct_freebsd($cpu)
		|| sct_netbsd($cpu)
		|| sct_openbsd($cpu)
		|| sct_hurd($cpu)
		|| sct_darwin($cpu)
		|| sct_solaris($cpu)
		|| sct_aix($cpu)
		|| sct_hpux($cpu)
		|| sct_qnx($cpu)
		|| sct_openserver($cpu)
		|| sct_irix($cpu)
		|| sct_tru64($cpu)
	    );
    }
    if(not $cpu) {
	# Fall back: Set all to nproc
	my $nproc = nproc();
	if($nproc) {
	    $cpu->{'sockets'} =
		$cpu->{'cores'} =
		$cpu->{'threads'} =
		$cpu->{'active'} =
		$nproc;
	}
    }
    if(not $cpu) {
	::warning("Cannot figure out number of cpus. Using 1.");
	$cpu->{'sockets'} =
	    $cpu->{'cores'} =
	    $cpu->{'threads'} =
	    $cpu->{'active'} =
	    1
    }
    $cpu->{'sockets'} ||= 1;
    $cpu->{'threads'} ||= $cpu->{'cores'};
    $cpu->{'active'} ||= $cpu->{'threads'};
    chomp($cpu->{'sockets'},
	  $cpu->{'cores'},
	  $cpu->{'threads'},
	  $cpu->{'active'});
    # Choose minimum of active and actual
    my $mincpu;
    $mincpu->{'sockets'} = ::min($cpu->{'sockets'},$cpu->{'active'});
    $mincpu->{'cores'} = ::min($cpu->{'cores'},$cpu->{'active'});
    $mincpu->{'threads'} = ::min($cpu->{'threads'},$cpu->{'active'});
    return $mincpu;
}

sub sct_gnu_linux($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    my $cpu = shift;

    sub read_topology($) {
	my $prefix = shift;
	my %sibiling;
	my %socket;
	my $thread;
	for($thread = 0;
	    -r "$prefix/cpu$thread/topology/physical_package_id";
	    $thread++) {
	    open(my $fh,"<",
		 "$prefix/cpu$thread/topology/physical_package_id")
		|| die;
	    $socket{<$fh>}++;
	    close $fh;
	}
	for($thread = 0;
	    -r "$prefix/cpu$thread/topology/thread_siblings";
	    $thread++) {
	    open(my $fh,"<",
		 "$prefix/cpu$thread/topology/thread_siblings")
		|| die;
	    $sibiling{<$fh>}++;
	    close $fh;
	}
	$cpu->{'sockets'} = keys %socket;
	$cpu->{'cores'} = keys %sibiling;
	$cpu->{'threads'} = $thread;
    }

    sub read_cpuinfo(@) {
	my @cpuinfo = @_;
	$cpu->{'sockets'} = 0;
	$cpu->{'cores'} = 0;
	$cpu->{'threads'} = 0;
	my %seen;
	my %phy_seen;
	my $physicalid;
	for(@cpuinfo) {
	    # physical id : 0
	    if(/^physical id.*[:](.*)/) {
		$physicalid = $1;
		if(not $phy_seen{$1}++) {
		    $cpu->{'sockets'}++;
		}
	    }
	    # core id : 3
	    if(/^core id.*[:](.*)/ and not $seen{$physicalid,$1}++) {
		$cpu->{'cores'}++;
	    }
	    # processor : 2
	    /^processor.*[:]\s*\d/i and $cpu->{'threads'}++;
	}
	$cpu->{'cores'} ||= $cpu->{'threads'};
	$cpu->{'cpus'} ||= $cpu->{'threads'};
	$cpu->{'sockets'} ||= 1;
    }

    sub read_lscpu(@) {
	my @lscpu = @_;
	my $threads_per_core;
	my $cores_per_socket;
	for(@lscpu) {
	    /^CPU.s.:\s*(\d+)/ and $cpu->{'threads'} = $1;
	    /^Thread.s. per core:\s*(\d+)/ and $threads_per_core = $1;
	    /^Core.s. per socket:\s*(\d+)/ and $cores_per_socket = $1;
	    /^(CPU )?Socket.s.:\s*(\d+)/i and $cpu->{'sockets'} = $2;
	}
	if($cores_per_socket and $cpu->{'sockets'}) {
	    $cpu->{'cores'} = $cores_per_socket * $cpu->{'sockets'};
	}
	if($threads_per_core and $cpu->{'cores'}) {
	    $cpu->{'threads'} = $threads_per_core * $cpu->{'cores'};
	}
	if($threads_per_core and $cpu->{'threads'}) {
	    $cpu->{'cores'} = $cpu->{'threads'} / $threads_per_core;
	}
	$cpu->{'cpus'} ||= $cpu->{'threads'};
    }

    local $/ = "\n"; # If delimiter is set, then $/ will be wrong
    my @cpuinfo;
    my @lscpu;
    if($ENV{'PARALLEL_CPUINFO'}) {
	# Use CPUINFO from environment - used for testing only
	read_cpuinfo(split/(?<=\n)/,$ENV{'PARALLEL_CPUINFO'});
    } elsif($ENV{'PARALLEL_LSCPU'}) {
	# Use LSCPU from environment - used for testing only
	read_lscpu(split/(?<=\n)/,$ENV{'PARALLEL_LSCPU'});
    } elsif(-r "$ENV{'PARALLEL_CPUPREFIX'}/cpu0/topology/thread_siblings") {
	# Use CPUPREFIX from environment - used for testing only
	read_topology($ENV{'PARALLEL_CPUPREFIX'});
    } elsif($cpu->{'sockets'} and $cpu->{'cores'} and $cpu->{'threads'}) {
	# Skip /proc/cpuinfo - already set
    } else {
	# Not debugging: Look at this computer
	if(!($cpu->{'sockets'} and $cpu->{'cores'} and $cpu->{'threads'})
	   and
	   open(my $in_fh, "-|", "lscpu")) {
	    # Parse output from lscpu
	    read_lscpu(<$in_fh>);
	    close $in_fh;
	}
	if(!($cpu->{'sockets'} and $cpu->{'cores'} and $cpu->{'threads'})
	   and
	   -r "/sys/devices/system/cpu/cpu0/topology/thread_siblings") {
	    read_topology("/sys/devices/system/cpu");
	}
	if(!($cpu->{'sockets'} and $cpu->{'cores'} and $cpu->{'threads'})
	   and
	   open(my $in_fh, "<", "/proc/cpuinfo")) {
	    # Read /proc/cpuinfo
	    read_cpuinfo(<$in_fh>);
	    close $in_fh;
	}
    }
    if(-e "/proc/self/status"
       and not $ENV{'PARALLEL_CPUINFO'}
       and not $ENV{'PARALLEL_LSCPU'}) {
	# if 'taskset' is used to limit number of threads
	if(open(my $in_fh, "<", "/proc/self/status")) {
	    while(<$in_fh>) {
		if(/^Cpus_allowed:\s*(\S+)/) {
		    my $a = $1;
		    $a =~ tr/,//d;
		    $cpu->{'active'} = unpack ("%32b*", pack ("H*",$a));
		}
	    }
	    close $in_fh;
	}
    }
    return $cpu;
}

sub sct_android($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    # Use GNU/Linux
    return sct_gnu_linux($_[0]);
}

sub sct_freebsd($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    $cpu->{'cores'} ||=
	(::qqx(qq{ sysctl -a dev.cpu | grep \%parent | awk '{ print \$2 }' | uniq | wc -l | awk '{ print \$1 }' })
	 or
	 ::qqx(qq{ sysctl hw.ncpu | awk '{ print \$2 }' }));
    $cpu->{'threads'} ||=
	(::qqx(qq{ sysctl hw.ncpu | awk '{ print \$2 }' })
	 or
	 ::qqx(qq{ sysctl -a dev.cpu | grep \%parent | awk '{ print \$2 }' | uniq | wc -l | awk '{ print \$1 }' }));
    return $cpu;
}

sub sct_netbsd($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    $cpu->{'cores'} ||= ::qqx("sysctl -n hw.ncpu");
    return $cpu;
}

sub sct_openbsd($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    $cpu->{'cores'} ||= ::qqx('sysctl -n hw.ncpu');
    return $cpu;
}

sub sct_hurd($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    $cpu->{'cores'} ||= ::qqx("nproc");
    return $cpu;
}

sub sct_darwin($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    $cpu->{'cores'} ||=
	(::qqx('sysctl -n hw.physicalcpu')
	 or
	 ::qqx(qq{ sysctl -a hw | grep [^a-z]physicalcpu[^a-z] | awk '{ print \$2 }' }));
    $cpu->{'threads'} ||=
	(::qqx('sysctl -n hw.logicalcpu')
	 or
	 ::qqx(qq{ sysctl -a hw | grep [^a-z]logicalcpu[^a-z] | awk '{ print \$2 }' }));
    return $cpu;
}

sub sct_solaris($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    if(not $cpu->{'cores'}) {
	if(-x "/usr/bin/kstat") {
	    my @chip_id = ::qqx("/usr/bin/kstat cpu_info|grep chip_id");
	    if($#chip_id >= 0) {
		$cpu->{'sockets'} ||= $#chip_id +1;
	    }
	    my @core_id = ::qqx("/usr/bin/kstat -m cpu_info|grep -w core_id|uniq");
	    if($#core_id >= 0) {
		$cpu->{'cores'} ||= $#core_id +1;
	    }
	}
	if(-x "/usr/sbin/psrinfo") {
	    my @psrinfo = ::qqx("/usr/sbin/psrinfo -p");
	    if($#psrinfo >= 0) {
		$cpu->{'sockets'} ||= $psrinfo[0];
	    }
	}
	if(-x "/usr/sbin/prtconf") {
	    my @prtconf = ::qqx("/usr/sbin/prtconf | grep cpu..instance");
	    if($#prtconf >= 0) {
		$cpu->{'cores'} ||= $#prtconf +1;
	    }
	}
    }
    return $cpu;
}

sub sct_aix($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    if(not $cpu->{'cores'}) {
	if(-x "/usr/sbin/lscfg") {
	    if(open(my $in_fh, "-|",
		    "/usr/sbin/lscfg -vs |grep proc | wc -l|tr -d ' '")) {
		$cpu->{'cores'} = <$in_fh>;
		close $in_fh;
	    }
	}
    }
    if(not $cpu->{'threads'}) {
	if(-x "/usr/bin/vmstat") {
	    if(open(my $in_fh, "-|", "/usr/bin/vmstat 1 1")) {
		while(<$in_fh>) {
		    /lcpu=([0-9]*) / and $cpu->{'threads'} = $1;
		}
		close $in_fh;
	    }
	}
    }
    return $cpu;
}

sub sct_hpux($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    $cpu->{'cores'} ||=
	::qqx(qq{ /usr/bin/mpsched -s 2>&1 | grep 'Locality Domain Count' | awk '{ print \$4 }'});
    $cpu->{'threads'} ||=
	::qqx(qq{ /usr/bin/mpsched -s 2>&1 | perl -ne '/Processor Count\\D+(\\d+)/ and print "\$1"'});
    return $cpu;
}

sub sct_qnx($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    # BUG: It is not known how to calculate this.

    return $cpu;
}

sub sct_openserver($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    if(not $cpu->{'cores'}) {
	if(-x "/usr/sbin/psrinfo") {
	    my @psrinfo = ::qqx("/usr/sbin/psrinfo");
	    if($#psrinfo >= 0) {
		$cpu->{'cores'} = $#psrinfo +1;
	    }
	}
    }
    $cpu->{'sockets'} ||= $cpu->{'cores'};
    return $cpu;
}

sub sct_irix($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    $cpu->{'cores'} ||=
	::qqx(qq{ hinv | grep HZ | grep Processor | awk '{print \$1}' });
    return $cpu;
}

sub sct_tru64($) {
    # Returns:
    #	{ 'sockets' => #sockets
    #	  'cores' => #cores
    #	  'threads' => #threads
    #	  'active' => #taskset_threads }
    local $/ = "\n";
    my $cpu = shift;
    $cpu->{'cores'} ||= ::qqx("sizer -pr");
    $cpu->{'sockets'} ||= $cpu->{'cores'};
    $cpu->{'threads'} ||= $cpu->{'cores'};

    return $cpu;
}

sub sshcommand($) {
    # Returns:
    #	$sshcommand = the command (incl options) to run when using ssh
    my $self = shift;
    if (not defined $self->{'sshcommand'}) {
	::die_bug("sshcommand not set");
    }
    return $self->{'sshcommand'};
}

sub local($) {
    my $self = shift;
    return $self->{'local'};
}

sub control_path_dir($) {
    # Returns:
    #	$control_path_dir = dir of control path (for -M)
    my $self = shift;
    if(not defined $self->{'control_path_dir'}) {
	$self->{'control_path_dir'} =
	    # Use $ENV{'TMPDIR'} as that is typically not
	    # NFS mounted.
	    # The file system must support UNIX domain sockets
	    File::Temp::tempdir($ENV{'TMPDIR'}
				. "/ctrlpath-XXXX",
				CLEANUP => 1);
    }
    return $self->{'control_path_dir'};
}

sub rsync_transfer_cmd($) {
    # Command to run to transfer a file
    # Input:
    #	$file = filename of file to transfer
    #	$workdir = destination dir
    # Returns:
    #	$cmd = rsync command to run to transfer $file ("" if unreadable)
    my $self = shift;
    my $file = shift;
    my $workdir = shift;
    if(not -r $file) {
	::warning($file. " is not readable and will not be transferred.");
	return "true";
    }
    my $rsync_destdir;
    my $relpath = ($file !~ m:^/:) || ($file =~ m:/\./:); # Is the path relative or /./?
    if($relpath) {
	$rsync_destdir = ::shell_quote_file($workdir);
    } else {
	# rsync /foo/bar /
	$rsync_destdir = "/";
    }
    $file = ::shell_quote_file($file);
    # Make dir if it does not exist
    return($self->wrap("mkdir -p $rsync_destdir") . " && " .
	   $self->rsync()." $file ".$self->{'host'}.":$rsync_destdir");
}

{
    my $rsync_fix;
    my $rsync_version;

    sub rsync($) {
	# rsync 3.1.x uses protocol 31 which is unsupported by 2.5.7.
	# If the version >= 3.1.0: downgrade to protocol 30
	# rsync 3.2.4 introduces a quoting bug: Add --old-args for that
	# Returns:
	#   $rsync = "rsync" or "rsync --protocol 30 --old-args"
	sub rsync_version {
	    if(not $rsync_version) {
		my @out = `rsync --version`;
		if(not @out) {
		    if(::which("rsync")) {
			::die_bug("'rsync --version' gave no output.");
		    } else {
			::error("'rsync' is not in \$PATH.");
			::wait_and_exit(255);
		    }
		}
		for (@out) {
		    # rsync	 version 3.1.3	protocol version 31
		    # rsync	 version v3.2.3	 protocol version 31
		    if(/version v?(\d+)\.(\d+)(\.(\d+))?/) {
			# 3.2.27 => 03.0227
			$rsync_version = sprintf "%02d.%02d%02d",$1,$2,$4;
		    }
		}
		$rsync_version or
		    ::die_bug("Cannot figure out version of rsync: @out");
	    }
	}

	sub rsync_fixup {
	    # rsync 3.1.x uses protocol 31 which is unsupported by 2.5.7.
	    # If the version >= 3.1.0: downgrade to protocol 30
	    # Returns:
	    #   $rsync = "rsync" or "rsync --protocol 30"
	    if(not $rsync_fix) {
		rsync_version();
		if($rsync_version >= 3.01) {
		    # Version 3.1.0 or later: Downgrade to protocol 30
		    $rsync_fix .= " --protocol 30";
		}
		if($rsync_version >= 3.0204) {
		    # Version 3.2.4 .. 3.2.8: --old-args
		    $rsync_fix .= " --old-args";
		}
	    }
	    return $rsync_fix;
	}
	my $self = shift;

	return "rsync".rsync_fixup()." ".$ENV{'PARALLEL_RSYNC_OPTS'}.
	    " -e".::Q($self->sshcmd());
    }
}

sub cleanup_cmd($$$) {
    # Command to run to remove the remote file
    # Input:
    #	$file = filename to remove
    #	$workdir = destination dir
    # Returns:
    #	$cmd = ssh command to run to remove $file and empty parent dirs
    my $self = shift;
    my $file = shift;
    my $workdir = shift;
    my $f = $file;
    if($f =~ m:/\./:) {
	# foo/bar/./baz/quux => workdir/baz/quux
	# /foo/bar/./baz/quux => workdir/baz/quux
	$f =~ s:.*/\./:$workdir/:;
    } elsif($f =~ m:^[^/]:) {
	# foo/bar => workdir/foo/bar
	$f = $workdir."/".$f;
    }
    my @subdirs = split m:/:, ::dirname($f);
    my @rmdir;
    my $dir = "";
    for(@subdirs) {
	$dir .= $_."/";
	unshift @rmdir, ::shell_quote_file($dir);
    }
    my $rmdir = @rmdir ? "rmdir @rmdir 2>/dev/null;" : "";
    if(defined $opt::workdir and $opt::workdir eq "...") {
	$rmdir .= "rm -rf " . ::shell_quote_file($workdir).';';
    }
    my $rmf = "sh -c ".
	::Q("rm -f ".::shell_quote_file($f)." 2>/dev/null;".$rmdir);
    return $self->wrap(::Q($rmf));
}

package JobQueue;

sub new($) {
    my $class = shift;
    my $commandref = shift;
    my $read_from = shift;
    my $context_replace = shift;
    my $max_number_of_args = shift;
    my $transfer_files = shift;
    my $return_files = shift;
    my $template_names = shift;
    my $template_contents = shift;
    my $commandlinequeue = CommandLineQueue->new
	($commandref, $read_from, $context_replace, $max_number_of_args,
	 $transfer_files, $return_files, $template_names, $template_contents);
    my @unget = ();
    return bless {
	'unget' => \@unget,
	'commandlinequeue' => $commandlinequeue,
	'this_job_no' => 0,
	'total_jobs' => undef,
    }, ref($class) || $class;
}

sub get($) {
    my $self = shift;

    $self->{'this_job_no'}++;
    if(@{$self->{'unget'}}) {
	my $job = shift @{$self->{'unget'}};
	# {%} may have changed, so flush computed values
	$job && $job->flush_cache();
	return $job;
    } else {
	my $commandline = $self->{'commandlinequeue'}->get();
	if(defined $commandline) {
	    return Job->new($commandline);
	} else {
	    $self->{'this_job_no'}--;
	    return undef;
	}
    }
}

sub unget($) {
    my $self = shift;
    unshift @{$self->{'unget'}}, @_;
    $self->{'this_job_no'} -= @_;
}

sub empty($) {
    my $self = shift;
    my $empty = (not @{$self->{'unget'}}) &&
	$self->{'commandlinequeue'}->empty();
    ::debug("run", "JobQueue->empty $empty ");
    return $empty;
}

sub total_jobs($) {
    my $self = shift;
    if(not defined $self->{'total_jobs'}) {
	if($opt::pipe and not $opt::tee) {
	    ::error("--pipe is incompatible with --eta/--bar/--shuf");
	    ::wait_and_exit(255);
	}
	if($opt::totaljobs) {
	    $self->{'total_jobs'} = $opt::totaljobs;
	} elsif($opt::sqlworker) {
	    $self->{'total_jobs'} = $Global::sql->total_jobs();
	} else {
	    my $record;
	    my @arg_records;
	    my $record_queue = $self->{'commandlinequeue'}{'arg_queue'};
	    my $start = time;
	    while($record = $record_queue->get()) {
		push @arg_records, $record;
		if(time - $start > 10) {
		    ::warning("Reading ".scalar(@arg_records).
			      " arguments took longer than 10 seconds.");
		    $opt::eta && ::warning("Consider removing --eta.");
		    $opt::bar && ::warning("Consider removing --bar.");
		    $opt::shuf && ::warning("Consider removing --shuf.");
		    last;
		}
	    }
	    while($record = $record_queue->get()) {
		push @arg_records, $record;
	    }
	    if($opt::shuf and @arg_records) {
		my $i = @arg_records;
		while (--$i) {
		    my $j = int rand($i+1);
		    @arg_records[$i,$j] = @arg_records[$j,$i];
		}
	    }
	    $record_queue->unget(@arg_records);
	    # $#arg_records = number of args - 1
	    # We have read one @arg_record for this job (so add 1 more)
	    my $num_args = $#arg_records + 2;
	    # This jobs is not started so -1
	    my $started_jobs = $self->{'this_job_no'} - 1;
	    my $max_args = ::max($Global::max_number_of_args,1);
	    $self->{'total_jobs'} = ::ceil($num_args / $max_args)
		+ $started_jobs;
	    ::debug("init","Total jobs: ".$self->{'total_jobs'}.
		    " ($num_args/$max_args + $started_jobs)\n");
	}
    }
    return $self->{'total_jobs'};
}

sub flush_total_jobs($) {
    # Unset total_jobs to force recomputing
    my $self = shift;
    ::debug("init","flush Total jobs: ");
    $self->{'total_jobs'} = undef;
}

sub next_seq($) {
    my $self = shift;

    return $self->{'commandlinequeue'}->seq();
}

sub quote_args($) {
    my $self = shift;
    return $self->{'commandlinequeue'}->quote_args();
}


package Job;

sub new($) {
    my $class = shift;
    my $commandlineref = shift;
    return bless {
	'commandline' => $commandlineref, # CommandLine object
	'workdir' => undef, # --workdir
	# filehandle for stdin (used for --pipe)
	# filename for writing stdout to (used for --files)
	# remaining data not sent to stdin (used for --pipe)
	# tmpfiles to cleanup when job is done
	'unlink' => [],
	# amount of data sent via stdin (used for --pipe)
	'transfersize' => 0, # size of files using --transfer
	'returnsize' => 0, # size of files using --return
	'pid' => undef,
	# hash of { SSHLogins => number of times the command failed there }
	'failed' => undef,
	'sshlogin' => undef,
	# The commandline wrapped with rsync and ssh
	'sshlogin_wrap' => undef,
	'exitstatus' => undef,
	'exitsignal' => undef,
	# Timestamp for timeout if any
	'timeout' => undef,
	'virgin' => 1,
	# Output used for SQL and CSV-output
	'output' => { 1 => [], 2 => [] },
	'halfline' => { 1 => [], 2 => [] },
    }, ref($class) || $class;
}

sub flush_cache($) {
    my $self = shift;
    $self->{'commandline'}->flush_cache();
}

sub replaced($) {
    my $self = shift;
    $self->{'commandline'} or ::die_bug("commandline empty");
    return $self->{'commandline'}->replaced();
}

{
    my $next_available_row;

    sub row($) {
	my $self = shift;
	if(not defined $self->{'row'}) {
	    if($opt::keeporder) {
		$self->{'row'} = $self->seq();
	    } else {
		$self->{'row'} = ++$next_available_row;
	    }
	}
	return $self->{'row'};
    }
}

sub seq($) {
    my $self = shift;
    return $self->{'commandline'}->seq();
}

sub set_seq($$) {
    my $self = shift;
    return $self->{'commandline'}->set_seq(shift);
}

sub slot($) {
    my $self = shift;
    return $self->{'commandline'}->slot();
}

sub free_slot($) {
    my $self = shift;
    push @Global::slots, $self->slot();
}

{
    my($cattail);

    sub cattail() {
	# Returns:
	#   $cattail = perl program for:
	#     cattail "decomp-prg" wpid [file_stdin] [file_to_unlink]
	#     decomp-prg     = decompress program
	#     wpid	     = pid of writer program
	#     file_stdin     = file_to_decompress
	#     file_to_unlink = unlink this file
	if(not $cattail) {
	    $cattail = q{
		# cat followed by tail (possibly with rm as soon at the file is opened)
		# If $writerpid dead: finish after this round
		use Fcntl;
		$|=1;

		my ($comfile, $cmd, $writerpid, $read_file, $unlink_file) = @ARGV;
		if($read_file) {
		    open(IN,"<",$read_file) || die("cattail: Cannot open $read_file");
		} else {
		    *IN = *STDIN;
		}
		while(! -s $comfile) {
		    # Writer has not opened the buffer file, so we cannot remove it yet
		    $sleep = ($sleep < 30) ? ($sleep * 1.001 + 0.01) : ($sleep);
		    usleep($sleep);
		}
		# The writer and we have both opened the file, so it is safe to unlink it
		unlink $unlink_file;
		unlink $comfile;

		my $first_round = 1;
		my $flags;
		fcntl(IN, F_GETFL, $flags) || die $!; # Get the current flags on the filehandle
		$flags |= O_NONBLOCK; # Add non-blocking to the flags
		fcntl(IN, F_SETFL, $flags) || die $!; # Set the flags on the filehandle

		while(1) {
		    # clear EOF
		    seek(IN,0,1);
		    my $writer_running = kill 0, $writerpid;
		    $read = sysread(IN,$buf,131072);
		    if($read) {
			if($first_round) {
			    # Only start the command if there any input to process
			    $first_round = 0;
			    open(OUT,"|-",$cmd) || die("cattail: Cannot run $cmd");
			}

			# Blocking print
			while($buf) {
			    my $bytes_written = syswrite(OUT,$buf);
			    # syswrite may be interrupted by SIGHUP
			    substr($buf,0,$bytes_written) = "";
			}
			# Something printed: Wait less next time
			$sleep /= 2;
		    } else {
			if(eof(IN) and not $writer_running) {
			    # Writer dead: There will never be sent more to the decompressor
			    close OUT;
			    exit;
			}
			# TODO This could probably be done more efficiently using select(2)
			# Nothing read: Wait longer before next read
			# Up to 100 milliseconds
			$sleep = ($sleep < 100) ? ($sleep * 1.001 + 0.01) : ($sleep);
			usleep($sleep);
		    }
		}

		sub usleep {
		    # Sleep this many milliseconds.
		    my $secs = shift;
		    select(undef, undef, undef, $secs/1000);
		}
	    };
	    $cattail =~ s/#.*//mg;
	    $cattail =~ s/\s+/ /g;
	}
	return $cattail;
    }
}

sub openoutputfiles($) {
    # Open files for STDOUT and STDERR
    # Set file handles in $self->fh
    my $self = shift;
    my ($outfhw, $errfhw, $outname, $errname);

    if($opt::latestline) {
	# Do not save to files: Use non-blocking pipe
	my ($outfhr, $errfhr);
	pipe($outfhr, $outfhw) || die;
	$self->set_fh(1,'w',$outfhw);
	$self->set_fh(2,'w',$outfhw);
	$self->set_fh(1,'r',$outfhr);
	$self->set_fh(2,'r',$outfhr);
	# Make it possible to read non-blocking from the pipe
	for my $fdno (1,2) {
	    ::set_fh_non_blocking($self->fh($fdno,'r'));
	}
	# Return immediately because we do not need setting filenames
	return;
    } elsif($Global::linebuffer and not
       ($opt::keeporder or $Global::files or $opt::results or
	$opt::compress or $opt::compress_program or
	$opt::decompress_program)) {
	# Do not save to files: Use non-blocking pipe
	my ($outfhr, $errfhr);
	pipe($outfhr, $outfhw) || die;
	pipe($errfhr, $errfhw) || die;
	$self->set_fh(1,'w',$outfhw);
	$self->set_fh(2,'w',$errfhw);
	$self->set_fh(1,'r',$outfhr);
	$self->set_fh(2,'r',$errfhr);
	# Make it possible to read non-blocking from the pipe
	for my $fdno (1,2) {
	    ::set_fh_non_blocking($self->fh($fdno,'r'));
	}
	# Return immediately because we do not need setting filenames
	return;
    } elsif($opt::results and not $Global::csvsep and not $Global::jsonout) {
	# If --results, but not --results *.csv/*.tsv
	my $out = $self->{'commandline'}->results_out();
	my $seqname;
	if($out eq $opt::results or $out =~ m:/$:) {
	    # $opt::results = simple string or ending in /
	    # => $out is a dir/
	    # prefix/name1/val1/name2/val2/seq
	    $seqname = $out."seq";
	    # prefix/name1/val1/name2/val2/stdout
	    $outname = $out."stdout";
	    # prefix/name1/val1/name2/val2/stderr
	    $errname = $out."stderr";
	} else {
	    # $opt::results = replacement string not ending in /
	    # => $out is a file
	    $outname = $out;
	    $errname = "$out.err";
	    $seqname = "$out.seq";
	}
	my $seqfhw;
	if(not open($seqfhw, "+>", $seqname)) {
	    ::error("Cannot write to `$seqname'.");
	    ::wait_and_exit(255);
	}
	print $seqfhw $self->seq();
	close $seqfhw;
	if(not open($outfhw, "+>", $outname)) {
	    ::error("Cannot write to `$outname'.");
	    ::wait_and_exit(255);
	}
	if(not open($errfhw, "+>", $errname)) {
	    ::error("Cannot write to `$errname'.");
	    ::wait_and_exit(255);
	}
	$self->set_fh(1,"unlink","");
	$self->set_fh(2,"unlink","");
	if($opt::sqlworker) {
	    # Save the filenames in SQL table
	    $Global::sql->update("SET Stdout = ?, Stderr = ? ".
				 "WHERE Seq = ". $self->seq(),
				 $outname, $errname);
	}
    } elsif(not $opt::ungroup) {
	# To group we create temporary files for STDOUT and STDERR
	# To avoid the cleanup unlink the files immediately (but keep them open)
	if($Global::files) {
	    ($outfhw, $outname) = ::tmpfile(SUFFIX => ".par");
	    ($errfhw, $errname) = ::tmpfile(SUFFIX => ".par");
	    # --files => only remove stderr
	    $self->set_fh(1,"unlink","");
	    $self->set_fh(2,"unlink",$errname);
	} else {
	    ($outfhw, $outname) = ::tmpfile(SUFFIX => ".par");
	    ($errfhw, $errname) = ::tmpfile(SUFFIX => ".par");
	    $self->set_fh(1,"unlink",$outname);
	    $self->set_fh(2,"unlink",$errname);
	}
    } else {
	# --ungroup
	open($outfhw,">&",$Global::fh{1}) || die;
	open($errfhw,">&",$Global::fh{2}) || die;
	# File name must be empty as it will otherwise be printed
	$outname = "";
	$errname = "";
	$self->set_fh(1,"unlink",$outname);
	$self->set_fh(2,"unlink",$errname);
    }
    # Set writing FD
    $self->set_fh(1,'w',$outfhw);
    $self->set_fh(2,'w',$errfhw);
    $self->set_fh(1,'name',$outname);
    $self->set_fh(2,'name',$errname);
    if($opt::compress) {
	$self->filter_through_compress();
    } elsif(not $opt::ungroup) {
	$self->grouped();
    }
    if($Global::linebuffer) {
	# Make it possible to read non-blocking from
	# the buffer files
	# Used for --linebuffer with -k, --files, --res, --compress*
	for my $fdno (1,2) {
	    ::set_fh_non_blocking($self->fh($fdno,'r'));
	}
    }
}

sub print_verbose_dryrun($) {
    # If -v set: print command to stdout (possibly buffered)
    # This must be done before starting the command
    my $self = shift;
    if($Global::verbose or $opt::dryrun) {
	my $fh = $self->fh(1,"w");
	if($Global::verbose <= 1) {
	    print $fh $self->replaced(),"\n";
	} else {
	    # Verbose level > 1: Print the rsync and stuff
	    print $fh $self->wrapped(),"\n";
	}
    }
    if($opt::sqlworker) {
	$Global::sql->update("SET Command = ? WHERE Seq = ".$self->seq(),
			     $self->replaced());
    }
}

sub add_rm($) {
    # Files to remove when job is done
    my $self = shift;
    push @{$self->{'unlink'}}, @_;
}

sub get_rm($) {
    # Files to remove when job is done
    my $self = shift;
    return @{$self->{'unlink'}};
}

sub cleanup($) {
    # Remove files when job is done
    my $self = shift;
    unlink $self->get_rm();
    delete @Global::unlink{$self->get_rm()};
}

sub grouped($) {
    my $self = shift;
    # Set reading FD if using --group (--ungroup does not need)
    for my $fdno (1,2) {
	# Re-open the file for reading
	# so fdw can be closed seperately
	# and fdr can be seeked seperately (for --line-buffer)
	open(my $fdr,"<", $self->fh($fdno,'name')) ||
	    ::die_bug("fdr: Cannot open ".$self->fh($fdno,'name'));
	$self->set_fh($fdno,'r',$fdr);
	# Unlink if not debugging
	$Global::debug or ::rm($self->fh($fdno,"unlink"));
    }
}

sub empty_input_wrapper($) {
    # If no input: exit(0)
    # If some input: Pass input as input to command on STDIN
    # This avoids starting the command if there is no input.
    # Input:
    #	$command = command to pipe data to
    # Returns:
    #	$wrapped_command = the wrapped command
    my $command = shift;
    # The optimal block size differs
    # It has been measured on:
    # AMD 6376: 59000
    # <big ppar --pipe --block 100M --test $1 -j1 'cat >/dev/null';
    my $script =
	::spacefree(0,q{
	    if(sysread(STDIN, $buf, 1)) {
		open($fh, "|-", @ARGV) || die;
		syswrite($fh, $buf);
		while($read = sysread(STDIN, $buf, 59000)) {
		    syswrite($fh, $buf);
		}
		close $fh;
		exit ($?&127 ? 128+($?&127) : 1+$?>>8)
	    }
		  });
    ::debug("run",'Empty wrap: perl -e '.::Q($script)."\n");
    if($Global::cshell
       and
       length $command > 499) {
	# csh does not like words longer than 1000 (499 quoted)
	# $command = "perl -e '".base64_zip_eval()."' ".
	# join" ",string_zip_base64(
	#	  'exec "'.::perl_quote_scalar($command).'"');
	return 'perl -e '.::Q($script)." ".
	    base64_wrap("exec \"$Global::shell\",'-c',\"".
				   ::perl_quote_scalar($command).'"');
    } else {
	return 'perl -e '.::Q($script)." ".
	    $Global::shell." -c ".::Q($command);
    }
}

sub filter_through_compress($) {
    my $self = shift;
    # Send stdout to stdin for $opt::compress_program(1)
    # Send stderr to stdin for $opt::compress_program(2)
    # cattail get pid:	$pid = $self->fh($fdno,'rpid');
    my $cattail = cattail();

    for my $fdno (1,2) {
	# Make a communication file.
	my ($fh, $comfile) = ::tmpfile(SUFFIX => ".pac");
	close $fh;
	# Compressor: (echo > $comfile; compress pipe) > output
	# When the echo is written to $comfile,
	# it is known that output file is opened,
	# thus output file can then be removed by the decompressor.
	# empty_input_wrapper is needed for plzip
	my $qcom = ::Q($comfile);
	my $wpid = open(my $fdw,"|-", "(echo > $qcom; ".
			empty_input_wrapper($opt::compress_program).") >".
			::Q($self->fh($fdno,'name'))) || die $?;
	$self->set_fh($fdno,'w',$fdw);
	$self->set_fh($fdno,'wpid',$wpid);
	# Decompressor: open output; -s $comfile > 0: rm $comfile output;
	#		decompress output > stdout
	my $rpid = open(my $fdr, "-|", "perl", "-e", $cattail, $comfile,
			$opt::decompress_program, $wpid,
			$self->fh($fdno,'name'),$self->fh($fdno,'unlink'))
	    || die $?;
	$self->set_fh($fdno,'r',$fdr);
	$self->set_fh($fdno,'rpid',$rpid);
    }
}

sub set_fh($$$$) {
    # Set file handle
    my ($self, $fd_no, $key, $fh) = @_;
    $self->{'fd'}{$fd_no,$key} = $fh;
}

sub fh($) {
    # Get file handle
    my ($self, $fd_no, $key) = @_;
    return $self->{'fd'}{$fd_no,$key};
}

sub write_block($) {
    my $self = shift;
    my $stdin_fh = $self->fh(0,"w");
    if(fork()) {
	# Close in parent
	close $stdin_fh;
    } else {
	# If writing is to a closed pipe:
	#   Do not call signal handler, but let nothing be written
	local $SIG{PIPE} = undef;

	for my $part (
	    grep { defined $_ }
	    $self->{'header'},$self->{'block'}) {
	    # syswrite may not write all in one go,
	    # so make sure everything is written.
	    my $written;
	    while($written = syswrite($stdin_fh,$$part)) {
		substr($$part,0,$written) = "";
	    }
	}
	close $stdin_fh;
	exit(0);
    }
}

sub write($) {
    my $self = shift;
    my $remaining_ref = shift;
    my $stdin_fh = $self->fh(0,"w");

    my $len = length $$remaining_ref;
    # syswrite may not write all in one go,
    # so make sure everything is written.
    my $written;

    # If writing is to a closed pipe:
    #	Do not call signal handler, but let nothing be written
    local $SIG{PIPE} = undef;
    while($written = syswrite($stdin_fh,$$remaining_ref)){
	substr($$remaining_ref,0,$written) = "";
    }
}

sub set_block($$$$$$) {
    # Copy stdin buffer from $block_ref up to $endpos
    # Prepend with $header_ref if virgin (i.e. not --roundrobin)
    # Remove $recstart and $recend if needed
    # Input:
    #	$header_ref = ref to $header to prepend
    #	$buffer_ref = ref to $buffer containing the block
    #	$endpos = length of $block to pass on
    #	$recstart = --recstart regexp
    #	$recend = --recend regexp
    # Returns:
    #	N/A
    my $self = shift;
    my ($header_ref,$buffer_ref,$endpos,$recstart,$recend) = @_;
    $self->{'header'} = $header_ref;
    if($opt::roundrobin or $opt::remove_rec_sep or defined $opt::retries) {
	my $a = "";
	if(($opt::roundrobin or defined $opt::retries) and $self->virgin()) {
	    $a .= $$header_ref;
	}
	# Job is no longer virgin
	$self->set_virgin(0);
	# Make a full copy because $buffer will change
	$a .= substr($$buffer_ref,0,$endpos);
	$self->{'block'} = \$a;
	if($opt::remove_rec_sep) {
	    remove_rec_sep($self->{'block'},$recstart,$recend);
	}
	$self->{'block_length'} = length ${$self->{'block'}};
    } else {
	$self->set_virgin(0);
	for(substr($$buffer_ref,0,$endpos)) {
	    $self->{'block'} = \$_;
	}
	$self->{'block_length'} = $endpos + length ${$self->{'header'}};
    }
    $self->{'block_pos'} = 0;
    $self->add_transfersize($self->{'block_length'});
}

sub block_ref($) {
    my $self = shift;
    return $self->{'block'};
}

sub block_length($) {
    my $self = shift;
    return $self->{'block_length'};
}

sub remove_rec_sep($) {
    # Remove --recstart and --recend from $block
    # Input:
    #	$block_ref = reference to $block to be modified
    #	$recstart = --recstart
    #	$recend = --recend
    # Uses:
    #	$opt::regexp = Are --recstart/--recend regexp?
    # Returns:
    #	N/A
    my ($block_ref,$recstart,$recend) = @_;
    # Remove record separator
    if($opt::regexp) {
	$$block_ref =~ s/$recend$recstart//gom;
	$$block_ref =~ s/^$recstart//os;
	$$block_ref =~ s/$recend$//os;
    } else {
	$$block_ref =~ s/\Q$recend$recstart\E//gom;
	$$block_ref =~ s/^\Q$recstart\E//os;
	$$block_ref =~ s/\Q$recend\E$//os;
    }
}

sub non_blocking_write($) {
    my $self = shift;
    my $something_written = 0;

    my $in = $self->fh(0,"w");
    my $rv = syswrite($in,
		      substr(${$self->{'block'}},$self->{'block_pos'}));
    if (!defined($rv) && $! == ::EAGAIN()) {
	# would block - but would have written
	$something_written = 0;
	# avoid triggering auto expanding block size
	$Global::no_autoexpand_block ||= 1;
    } elsif ($self->{'block_pos'}+$rv != $self->{'block_length'}) {
	# incomplete write
	# Remove the written part
	$self->{'block_pos'} += $rv;
	$something_written = $rv;
    } else {
	# successfully wrote everything
	# Empty block to free memory
	my $a = "";
	$self->set_block(\$a,\$a,0,"","");
	$something_written = $rv;
    }
    ::debug("pipe", "Non-block: ", $something_written);
    return $something_written;
}


sub virgin($) {
    my $self = shift;
    return $self->{'virgin'};
}

sub set_virgin($$) {
    my $self = shift;
    $self->{'virgin'} = shift;
}

sub pid($) {
    my $self = shift;
    return $self->{'pid'};
}

sub set_pid($$) {
    my $self = shift;
    $self->{'pid'} = shift;
}

sub starttime($) {
    # Returns:
    #	UNIX-timestamp this job started
    my $self = shift;
    return sprintf("%.3f",$self->{'starttime'});
}

sub set_starttime($@) {
    my $self = shift;
    my $starttime = shift || ::now();
    $self->{'starttime'} = $starttime;
    $opt::sqlworker and
	$Global::sql->update("SET Starttime = ? WHERE Seq = ".$self->seq(),
			     $starttime);
}

sub runtime($) {
    # Returns:
    #	Run time in seconds with 3 decimals
    my $self = shift;
    return sprintf("%.3f",
		   int(($self->endtime() - $self->starttime())*1000)/1000);
}

sub endtime($) {
    # Returns:
    #	UNIX-timestamp this job ended
    #	0 if not ended yet
    my $self = shift;
    return ($self->{'endtime'} || 0);
}

sub set_endtime($$) {
    my $self = shift;
    my $endtime = shift;
    $self->{'endtime'} = $endtime;
    $opt::sqlworker and
	$Global::sql->update("SET JobRuntime = ? WHERE Seq = ".$self->seq(),
			     $self->runtime());
}

sub is_timedout($) {
    # Is the job timedout?
    # Input:
    #	$delta_time = time that the job may run
    # Returns:
    #	True or false
    my $self = shift;
    my $delta_time = shift;
    return time > $self->{'starttime'} + $delta_time;
}

sub kill($) {
    my $self = shift;
    $self->set_exitstatus(-1);
    ::kill_sleep_seq($self->pid());
}

sub suspend($) {
    my $self = shift;
    my @pgrps = map { -$_ } $self->pid();
    kill "STOP", @pgrps;
    $self->set_suspended(1);
}

sub set_suspended($$) {
    my $self = shift;
    $self->{'suspended'} = shift;
}

sub suspended($) {
    my $self = shift;
    return $self->{'suspended'};
}

sub resume($) {
    my $self = shift;
    my @pgrps = map { -$_ } $self->pid();
    kill "CONT", @pgrps;
    $self->set_suspended(0);
}

sub failed($) {
    # return number of times failed for this $sshlogin
    # Input:
    #	$sshlogin
    # Returns:
    #	Number of times failed for $sshlogin
    my $self = shift;
    my $sshlogin = shift;
    return $self->{'failed'}{$sshlogin};
}

sub failed_here($) {
    # return number of times failed for the current $sshlogin
    # Returns:
    #	Number of times failed for this sshlogin
    my $self = shift;
    return $self->{'failed'}{$self->sshlogin()};
}

sub add_failed($) {
    # increase the number of times failed for this $sshlogin
    my $self = shift;
    my $sshlogin = shift;
    $self->{'failed'}{$sshlogin}++;
}

sub add_failed_here($) {
    # increase the number of times failed for the current $sshlogin
    my $self = shift;
    $self->{'failed'}{$self->sshlogin()}++;
}

sub reset_failed($) {
    # increase the number of times failed for this $sshlogin
    my $self = shift;
    my $sshlogin = shift;
    delete $self->{'failed'}{$sshlogin};
}

sub reset_failed_here($) {
    # increase the number of times failed for this $sshlogin
    my $self = shift;
    delete $self->{'failed'}{$self->sshlogin()};
}

sub min_failed($) {
    # Returns:
    #	the number of sshlogins this command has failed on
    #	the minimal number of times this command has failed
    my $self = shift;
    my $min_failures =
	::min(map { $self->{'failed'}{$_} } keys %{$self->{'failed'}});
    my $number_of_sshlogins_failed_on = scalar keys %{$self->{'failed'}};
    return ($number_of_sshlogins_failed_on,$min_failures);
}

sub total_failed($) {
    # Returns:
    #	$total_failures = the number of times this command has failed
    my $self = shift;
    my $total_failures = 0;
    for (values %{$self->{'failed'}}) {
	$total_failures += $_;
    }
    return $total_failures;
}

{
    my $script;

    sub postpone_exit_and_cleanup {
	# Command to remove files and dirs (given as args) without
	# affecting the exit value in $?/$status.
	if(not $script) {
	    $script = "perl -e '".
		::spacefree(0,q{
		    $bash=shift;
		    $csh=shift;
		    for(@ARGV){
			unlink;
			rmdir;
		    }
		    if($bash=~s/(\d+)h/$1/) {
			exit $bash;
		    }
		    exit $csh;
			    }).
		# `echo \$?h` is needed to make fish not complain
		"' ".'"`echo \\\\\\\\\$?h`" "$status" ';
	}
	return $script
    }
}

{
    my $script;

    sub fifo_wrap() {
	# Script to create a fifo, run a command on the fifo
	# while copying STDIN to the fifo, and finally
	# remove the fifo and return the exit code of the command.
	if(not $script) {
	    # {} == $PARALLEL_TMP for --fifo
	    # To make it csh compatible a wrapper needs to:
	    # * mkfifo
	    # * spawn $command &
	    # * cat > fifo
	    # * waitpid to get the exit code from $command
	    # * be less than 1000 chars long

	    # The optimal block size differs
	    # It has been measured on:
	    # AMD 6376: 4095
	    # ppar -a big --pipepart --block -1 --test $1 --fifo 'cat {} >/dev/null';
	    $script = "perl -e '".
		(::spacefree
		 (0, q{
		     ($s,$c,$f) = @ARGV;
		     # mkfifo $PARALLEL_TMP
		     system "mkfifo", $f;
		     # spawn $shell -c $command &
		     $pid = fork || exec $s, "-c", $c;
		     open($o,">",$f) || die $!;
		     # cat > $PARALLEL_TMP
		     while(sysread(STDIN,$buf,4095)){
			 syswrite $o, $buf;
		     }
		     close $o;
		     # waitpid to get the exit code from $command
		     waitpid $pid,0;
		     # Cleanup
		     unlink $f;
		     exit $?/256;
		  }))."'";
	}
	return $script;
    }
}

sub wrapped($) {
    # Wrap command with:
    # * --shellquote
    # * --nice
    # * --cat
    # * --fifo
    # * --sshlogin
    # * --pipepart (@Global::cat_prepends)
    # * --tee (@Global::cat_prepends)
    # * --pipe
    # * --tmux
    # The ordering of the wrapping is important:
    # * --nice/--cat/--fifo should be done on the remote machine
    # * --pipepart/--pipe should be done on the local machine inside --tmux
    # Uses:
    #	@opt::shellquote
    #	$opt::nice
    #	$Global::shell
    #	$opt::cat
    #	$opt::fifo
    #	@Global::cat_prepends
    #	$opt::pipe
    #	$opt::tmux
    # Returns:
    #	$self->{'wrapped'} = the command wrapped with the above
    my $self = shift;
    if(not defined $self->{'wrapped'}) {
	my $command = $self->replaced();
	# Bug in Bash and Ksh when running multiline aliases
	# This will force them to run correctly, but will fail in
	# tcsh so we do not do it.
	# $command .= "\n\n";
	if(@opt::shellquote) {
	    # Quote one time for each --shellquote
	    my $c = $command;
	    for(@opt::shellquote) {
		$c = ::Q($c);
	    }
	    # Prepend "echo" (it is written in perl because
	    # quoting '-e' causes problem in some versions and
	    # csh's version does something wrong)
	    $command = q(perl -e '$,=" "; print "@ARGV\n";' -- ) . ::Q($c);
	}
	if($Global::parallel_env) {
	    # If $PARALLEL_ENV set, put that in front of the command
	    # Used for env_parallel.*
	    if($Global::shell =~ /zsh/) {
		# The extra 'eval' will make aliases work, too
		$command = $Global::parallel_env."\n".
		    "eval ".::Q($command);
	    } else {
		$command = $Global::parallel_env."\n".$command;
	    }
	}
	if($opt::cat) {
	    # In '--cat' and '--fifo' {} == $PARALLEL_TMP.
	    # This is to make it possible to compute $PARALLEL_TMP on
	    # the fly when running remotely.
	    # $ENV{PARALLEL_TMP} is set in the remote wrapper before
	    # the command is run.
	    #
	    # Prepend 'cat > $PARALLEL_TMP;'
	    # Append 'unlink $PARALLEL_TMP without affecting $?'
	    $command =
		'cat > "$PARALLEL_TMP";'.
		$command.";". postpone_exit_and_cleanup().
					 '"$PARALLEL_TMP"';
	} elsif($opt::fifo) {
	    # Prepend fifo-wrapper. In essence:
	    #	mkfifo {}
	    #	( $command ) &
	    #	# $command must read {}, otherwise this 'cat' will block
	    #	cat > {};
	    #	wait; rm {}
	    # without affecting $?
	    $command = fifo_wrap(). " ".
		$Global::shell. " ". ::Q($command). ' "$PARALLEL_TMP"'. ';';
	}
	# Wrap with ssh + tranferring of files
	$command = $self->sshlogin_wrap($command);
	if(@Global::cat_prepends) {
	    # --pipepart: prepend:
	    # < /tmp/foo perl -e 'while(@ARGV) {
	    #	sysseek(STDIN,shift,0) || die; $left = shift;
	    #	while($read = sysread(STDIN,$buf, ($left > 60800 ? 60800 : $left))){
	    #	  $left -= $read; syswrite(STDOUT,$buf);
	    #	}
	    # }'  0 0 0 11 |
	    #
	    # --pipepart --tee: prepend:
	    #	< dash-a-file
	    #
	    # --pipe --tee: wrap:
	    #	(rm fifo; ... ) < fifo
	    #
	    # --pipe --shard X:
	    #	(rm fifo; ... ) < fifo
	    $command = (shift @Global::cat_prepends). "($command)".
		(shift @Global::cat_appends);
	} elsif($opt::pipe and not $opt::roundrobin) {
	    # Wrap with EOF-detector to avoid starting $command if EOF.
	    $command = empty_input_wrapper($command);
	}
	if($opt::tmux) {
	    # Wrap command with 'tmux'
	    $command = $self->tmux_wrap($command);
	}
	if($Global::cshell
	   and
	   length $command > 499) {
	    # csh does not like words longer than 1000 (499 quoted)
	    # $command = "perl -e '".base64_zip_eval()."' ".
	    # join" ",string_zip_base64(
	    #	      'exec "'.::perl_quote_scalar($command).'"');
	    $command = base64_wrap("exec \"$Global::shell\",'-c',\"".
				   ::perl_quote_scalar($command).'"');
	}
	$self->{'wrapped'} = $command;
    }
    return $self->{'wrapped'};
}

sub set_sshlogin($$) {
    my $self = shift;
    my $sshlogin = shift;
    $self->{'sshlogin'} = $sshlogin;
    delete $self->{'sshlogin_wrap'}; # If sshlogin is changed the wrap is wrong
    delete $self->{'wrapped'};

    if($opt::sqlworker) {
	# Identify worker as --sqlworker often runs on different machines
	# If local: Use hostname
	my $host = $sshlogin->local() ? ::hostname() : $sshlogin->host();
	$Global::sql->update("SET Host = ? WHERE Seq = ".$self->seq(), $host);
    }
}

sub sshlogin($) {
    my $self = shift;
    return $self->{'sshlogin'};
}

sub string_base64($) {
    # Base64 encode strings into 1000 byte blocks.
    # 1000 bytes is the largest word size csh supports
    # Input:
    #	@strings = to be encoded
    # Returns:
    #	@base64 = 1000 byte block
    $Global::use{"MIME::Base64"} ||= eval "use MIME::Base64; 1;";
    my @base64 = unpack("(A1000)*",encode_base64((join"",@_),""));
    return @base64;
}

sub string_zip_base64($) {
    # Pipe string through 'bzip2 -9' and base64 encode it into 1000
    # byte blocks.
    # 1000 bytes is the largest word size csh supports
    # Zipping will make exporting big environments work, too
    # Input:
    #	@strings = to be encoded
    # Returns:
    #	@base64 = 1000 byte block
    my($zipin_fh, $zipout_fh,@base64);
    ::open3($zipin_fh,$zipout_fh,">&STDERR","bzip2 -9");
    if(fork) {
	close $zipin_fh;
	$Global::use{"MIME::Base64"} ||= eval "use MIME::Base64; 1;";
	# Split base64 encoded into 1000 byte blocks
	@base64 = unpack("(A1000)*",encode_base64((join"",<$zipout_fh>),""));
	close $zipout_fh;
    } else {
	close $zipout_fh;
	print $zipin_fh @_;
	close $zipin_fh;
	exit;
    }
    ::debug("base64","Orig:@_\nAs bzip2 base64:@base64\n");
    return @base64;
}

sub base64_zip_eval() {
    # Script that:
    #	* reads base64 strings from @ARGV
    #	* decodes them
    #	* pipes through 'bzip2 -dc'
    #	* evals the result
    # Reverse of string_zip_base64 + eval
    # Will be wrapped in ' so single quote is forbidden
    # Returns:
    #	$script = 1-liner for perl -e
    my $script = ::spacefree(0,q{
	@GNU_Parallel = split /_/, "use_IPC::Open3;_use_MIME::Base64";
	eval"@GNU_Parallel";
	$chld = $SIG{CHLD};
	$SIG{CHLD} = "IGNORE";
	# Search for bzip2. Not found => use default path
	my $zip = (grep { -x $_ } "/usr/local/bin/bzip2")[0] || "bzip2";
	# $in = stdin on $zip, $out = stdout from $zip
	# Forget my() to save chars for csh
	# my($in, $out,$eval);
	open3($in,$out,">&STDERR",$zip,"-dc");
	if(my $perlpid = fork) {
	    close $in;
	    $eval = join "", <$out>;
	    close $out;
	} else {
	    close $out;
	    # Pipe decoded base64 into 'bzip2 -dc'
	    print $in (decode_base64(join"",@ARGV));
	    close $in;
	    exit;
	}
	wait;
	$SIG{CHLD} = $chld;
	eval $eval;
			     });
    ::debug("base64",$script,"\n");
    return $script;
}

sub base64_wrap($) {
    # base64 encode Perl code
    # Split it into chunks of < 1000 bytes
    # Prepend it with a decoder that eval's it
    # Input:
    #	$eval_string = Perl code to run
    # Returns:
    #	$shell_command = shell command that runs $eval_string
    my $eval_string = shift;
    return
	"perl -e ".
	::Q(base64_zip_eval())." ".
	join" ",::shell_quote(string_zip_base64($eval_string));
}

sub base64_eval($) {
    # Script that:
    #	* reads base64 strings from @ARGV
    #	* decodes them
    #	* evals the result
    # Reverse of string_base64 + eval
    # Will be wrapped in ' so single quote is forbidden.
    # Spaces are stripped so spaces cannot be significant.
    # The funny 'use IPC::Open3'-syntax is to avoid spaces and
    # to make it clear that this is a GNU  Parallel command
    # when looking at the process table.
    # Returns:
    #	$script = 1-liner for perl -e
    my $script = ::spacefree(0,q{
	@GNU_Parallel=("use","IPC::Open3;","use","MIME::Base64");
	eval "@GNU_Parallel";
	my $eval = decode_base64(join"",@ARGV);
	eval $eval;
			     });
    ::debug("base64",$script,"\n");
    return $script;
}

sub sshlogin_wrap($) {
    # Wrap the command with the commands needed to run remotely
    # Input:
    #	$command = command to run
    # Returns:
    #	$self->{'sshlogin_wrap'} = command wrapped with ssh+transfer commands
    sub monitor_parent_sshd_script {
	# This script is to solve the problem of
	# * not mixing STDERR and STDOUT
	# * terminating with ctrl-c
	# If its parent is ssh: all good
	# If its parent is init(1): ssh died, so kill children
	my $monitor_parent_sshd_script;

	if(not $monitor_parent_sshd_script) {
	    $monitor_parent_sshd_script =
		# This will be packed in ', so only use "
		::spacefree
		(0,'$shell = "'.($ENV{'PARALLEL_SHELL'} || '$ENV{SHELL}').'";'.
			    '$tmpdir = $ENV{"TMPDIR"} || "'.
			    ::perl_quote_scalar($ENV{'PARALLEL_REMOTE_TMPDIR'}).'";'.
			    '$nice = '.$opt::nice.';'.
			    '$termseq = "'.$opt::termseq.'";'.
			    # }
			    q{
		# Check that $tmpdir is writable
		-w $tmpdir ||
		    die("$tmpdir\040is\040not\040writable.".
			"\040Set\040PARALLEL_REMOTE_TMPDIR");
		# Set $PARALLEL_TMP to a non-existent file name in $TMPDIR
		do {
		    $ENV{PARALLEL_TMP} = $tmpdir."/par".
			join"", map { (0..9,"a".."z","A".."Z")[rand(62)] } (1..5);
		} while(-e $ENV{PARALLEL_TMP});
		# Set $script to a non-existent file name in $TMPDIR
		do {
		    $script = $tmpdir."/par-job-$ENV{PARALLEL_SEQ}_".
			join"", map { (0..9,"a".."z","A".."Z")[rand(62)] } (1..5);
		} while(-e $script);
		# Create a script from the hex code
		# that removes itself and runs the commands
		open($fh,">",$script) || die;
		# \040 = space - but we remove spaces in the script
		# ' needed due to rc-shell
		print($fh("rm\040\'$script\'\n",$bashfunc.$cmd));
		close $fh;
		my $parent = getppid;
		my $done = 0;
		$SIG{CHLD} = sub { $done = 1; };
		$pid = fork;
		unless($pid) {
		    # Make own process group to be able to kill HUP it later
		    eval { setpgrp };
		    # Set nice value
		    eval { setpriority(0,0,$nice) };
		    # Run the script
		    exec($shell,$script);
		    die("exec\040failed: $!");
		}
		while((not $done) and (getppid == $parent)) {
		    # Parent pid is not changed, so sshd is alive
		    # Exponential sleep up to 1 sec
		    $s = $s < 1 ? 0.001 + $s * 1.03 : $s;
		    select(undef, undef, undef, $s);
		}
		if(not $done) {
		    # sshd is dead: User pressed Ctrl-C
		    # Kill as per --termseq
		    my @term_seq = split/,/,$termseq;
		    if(not @term_seq) {
			@term_seq = ("TERM",200,"TERM",100,"TERM",50,"KILL",25);
		    }
		    while(@term_seq && kill(0,-$pid)) {
			kill(shift @term_seq, -$pid);
			select(undef, undef, undef, (shift @term_seq)/1000);
		    }
		}
		wait;
		exit ($?&127 ? 128+($?&127) : 1+$?>>8)
	    });
	}
	return $monitor_parent_sshd_script;
    }

    sub vars_to_export {
	# Uses:
	#   @opt::env
	my @vars = ("parallel_bash_environment");
	for my $varstring (@opt::env) {
	    # Split up --env VAR1,VAR2
	    push @vars, split /,/, $varstring;
	}
	for (@vars) {
	    if(-r $_ and not -d) {
		# Read as environment definition bug #44041
		# TODO parse this
		my $fh = ::open_or_exit($_);
		$Global::envdef = join("",<$fh>);
		close $fh;
	    }
	}
	if(grep { /^_$/ } @vars) {
	    local $/ = "\n";
	    # --env _
	    # Include all vars that are not in a clean environment
	    if(open(my $vars_fh, "<", $Global::config_dir . "/ignored_vars")) {
		my @ignore = <$vars_fh>;
		chomp @ignore;
		my %ignore;
		@ignore{@ignore} = @ignore;
		close $vars_fh;
		push @vars, grep { not defined $ignore{$_} } keys %ENV;
		@vars = grep { not /^_$/ } @vars;
	    } else {
		::error("Run '$Global::progname --record-env' ".
			"in a clean environment first.");
		::wait_and_exit(255);
	    }
	}
	# Duplicate vars as BASH functions to include post-shellshock functions (v1+v2)
	# So --env myfunc should look for BASH_FUNC_myfunc() and BASH_FUNC_myfunc%%

	push(@vars, "PARALLEL_PID", "PARALLEL_SEQ",
	     "PARALLEL_SSHLOGIN", "PARALLEL_SSHHOST",
	     "PARALLEL_HOSTGROUPS", "PARALLEL_ARGHOSTGROUPS",
	     "PARALLEL_JOBSLOT", $opt::process_slot_var,
	     map { ("BASH_FUNC_$_()", "BASH_FUNC_$_%%") } @vars);
	# Keep only defined variables
	return grep { defined($ENV{$_}) } @vars;
    }

    sub env_as_eval {
	# Returns:
	#   $eval = '$ENV{"..."}=...; ...'
	my @vars = vars_to_export();
	my $csh_friendly = not grep { /\n/ } @ENV{@vars};
	my @bash_functions = grep { substr($ENV{$_},0,4) eq "() {" } @vars;
	my @non_functions = (grep { !/PARALLEL_ENV/ }
			     grep { substr($ENV{$_},0,4) ne "() {" } @vars);

	# eval of @envset will set %ENV
	my $envset = join"", map {
	    '$ENV{"'.::perl_quote_scalar($_).'"}="'.
		::perl_quote_scalar($ENV{$_}).'";'; } @non_functions;

	# running @bashfunc on the command line, will set the functions
	my @bashfunc = map {
	    my $v=$_;
	    s/BASH_FUNC_(.*)(\(\)|%%)/$1/;
	    "$_$ENV{$v};\nexport -f $_ 2> /dev/null;\n" } @bash_functions;
	# eval $bashfuncset will set $bashfunc
	my $bashfuncset;
	if(@bashfunc) {
	    # Functions are not supported for all shells
	    if($Global::shell !~ m:(^|/)(ash|bash|rbash|zsh|rzsh|dash|ksh):) {
		::warning("Shell functions may not be supported in $Global::shell.");
	    }
	    $bashfuncset =
		'@bash_functions=qw('."@bash_functions".");".
		::spacefree(1,'$shell="'.($ENV{'PARALLEL_SHELL'} || '$ENV{SHELL}').'";'.q{
		    if($shell=~/csh/) {
			print STDERR "CSH/TCSH DO NOT SUPPORT newlines IN VARIABLES/FUNCTIONS. Unset @bash_functions\n";
			exec "false";
		    }
			    }).
				"\n".'$bashfunc = "'.::perl_quote_scalar("@bashfunc").'";';
	} else {
	    $bashfuncset = '$bashfunc = "";'
	}
	if($ENV{'parallel_bash_environment'}) {
	    $bashfuncset .= '$bashfunc .= "eval\ \"\$parallel_bash_environment\"\;";';
	}
	::debug("base64",$envset,$bashfuncset,"\n");
	return $csh_friendly,$envset,$bashfuncset;
    }

    my $self = shift;
    my $command = shift;
    # TODO test that *sh -c 'parallel --env' use *sh
    if(not defined $self->{'sshlogin_wrap'}{$command}) {
	my $sshlogin = $self->sshlogin();
	$ENV{'PARALLEL_SEQ'} = $self->seq();
	$ENV{$opt::process_slot_var} = -1 +
	    ($ENV{'PARALLEL_JOBSLOT'} = $self->slot());
	$ENV{'PARALLEL_SSHLOGIN'} = $sshlogin->string();
	$ENV{'PARALLEL_SSHHOST'} = $sshlogin->host();
	if ($opt::hostgroups) {
	    $ENV{'PARALLEL_HOSTGROUPS'} = join '+', $sshlogin->hostgroups();
	    $ENV{'PARALLEL_ARGHOSTGROUPS'} = join '+', $self->hostgroups();
	}
	$ENV{'PARALLEL_PID'} = $$;
	if($sshlogin->local()) {
	    if($opt::workdir) {
		# Create workdir if needed. Then cd to it.
		my $wd = $self->workdir();
		if($opt::workdir eq "." or $opt::workdir eq "...") {
		    # If $wd does not start with '/': Prepend $HOME
		    $wd =~ s:^([^/]):$ENV{'HOME'}/$1:;
		}
		::mkdir_or_die($wd);
		my $post = "";
		if($opt::workdir eq "...") {
		    $post = ";".exitstatuswrapper("rm -rf ".::Q($wd).";");

		}
		$command = "cd ".::Q($wd)." || exit 255; " .
		    $command . $post;;
	    }
	    if(@opt::env) {
		# Prepend with environment setter, which sets functions in zsh
		my ($csh_friendly,$envset,$bashfuncset) = env_as_eval();
		my $perl_code = $envset.$bashfuncset.
		    '@ARGV="'.::perl_quote_scalar($command).'";'.
		    "exec\"$Global::shell\",\"-c\",\(\$bashfunc.\"\@ARGV\"\)\;die\"exec:\$\!\\n\"\;";
		if(length $perl_code > 999
		   or
		   not $csh_friendly
		   or
		   $command =~ /\n/) {
		    # csh does not deal well with > 1000 chars in one word
		    # csh does not deal well with $ENV with \n
		    $self->{'sshlogin_wrap'}{$command} = base64_wrap($perl_code);
		} else {
		    $self->{'sshlogin_wrap'}{$command} = "perl -e ".::Q($perl_code);
		}
	    } else {
		$self->{'sshlogin_wrap'}{$command} = $command;
	    }
	} else {
	    my $pwd = "";
	    if($opt::workdir) {
		# Create remote workdir if needed. Then cd to it.
		my $wd = ::pQ($self->workdir());
		$pwd = qq{system("mkdir","-p","--","$wd"); chdir "$wd" ||}.
		    qq{print(STDERR "parallel: Cannot chdir to $wd\\n") &&}.
		    qq{exit 255;};
	    }
	    my ($csh_friendly,$envset,$bashfuncset) = env_as_eval();
	    my $cmd = $command;
	    # q// does not quote \, so we must do that
	    $cmd =~ s/\\/\\\\/g;

	    my $remote_command = $sshlogin->hexwrap
		($pwd.$envset.$bashfuncset.'$cmd='."q\0".$cmd."\0;".
		 monitor_parent_sshd_script());
	    my ($pre,$post,$cleanup)=("","","");
	    # --transfer
	    $pre .= $self->sshtransfer();
	    # --return
	    $post .= $self->sshreturn();
	    # --cleanup
	    $post .= $self->sshcleanup();
	    if($post) {
		# We need to save the exit status of the job
		$post = exitstatuswrapper($post);
	    }
	    $self->{'sshlogin_wrap'}{$command} =
		($pre
		 . $sshlogin->wrap($remote_command)
		 . ";"
		 . $post);
	}
    }
    return $self->{'sshlogin_wrap'}{$command};
}

sub fill_templates($) {
    # Replace replacement strings in template(s)
    # Returns:
    #	@templates - File names of replaced templates
    my $self = shift;

    if(%opt::template) {
	my @template_name =
	    map { $self->{'commandline'}->replace_placeholders([$_],0,0) }
	@{$self->{'commandline'}{'template_names'}};
	::debug("tmpl","Names: @template_name\n");
	for(my $i = 0; $i <= $#template_name; $i++) {
	    open(my $fh, ">", $template_name[$i]) || die;
	    print $fh $self->{'commandline'}->
		replace_placeholders([$self->{'commandline'}
				      {'template_contents'}[$i]],0,0);
	    close $fh;
	}
	if($opt::cleanup) {
	    $self->add_rm(@template_name);
	}
    }
}

sub filter($) {
    # Replace replacement strings in filter(s) and evaluate them
    # Returns:
    #	$run - 1=yes, undef=no
    my $self = shift;
    my $run = 1;
    if(@opt::filter) {
	for my $eval ($self->{'commandline'}->
		      replace_placeholders(\@opt::filter,0,0)) {
	    $run &&= eval $eval;
	}
	$self->{'commandline'}{'skip'} ||= not $run;
    }
    return $run;
}

sub transfer($) {
    # Files to transfer
    # Non-quoted and with {...} substituted
    # Returns:
    #	@transfer - File names of files to transfer
    my $self = shift;

    my $transfersize = 0;
    my @transfer = $self->{'commandline'}->
	replace_placeholders($self->{'commandline'}{'transfer_files'},0,0);
    for(@transfer) {
	# filesize
	if(-e $_) {
	    $transfersize += (stat($_))[7];
	}
    }
    $self->add_transfersize($transfersize);
    return @transfer;
}

sub transfersize($) {
    my $self = shift;
    return $self->{'transfersize'};
}

sub add_transfersize($) {
    my $self = shift;
    my $transfersize = shift;
    $self->{'transfersize'} += $transfersize;
    $opt::sqlworker and
	$Global::sql->update("SET Send = ? WHERE Seq = ".$self->seq(),
			     $self->{'transfersize'});
}

sub sshtransfer($) {
    # Returns for each transfer file:
    #	rsync $file remote:$workdir
    my $self = shift;
    my @pre;
    my $sshlogin = $self->sshlogin();
    my $workdir = $self->workdir();
    for my $file ($self->transfer()) {
	push @pre, $sshlogin->rsync_transfer_cmd($file,$workdir).";";
    }
    return join("",@pre);
}

sub return($) {
    # Files to return
    # Non-quoted and with {...} substituted
    # Returns:
    #	@non_quoted_filenames
    my $self = shift;
    return $self->{'commandline'}->
	replace_placeholders($self->{'commandline'}{'return_files'},0,0);
}

sub returnsize($) {
    # This is called after the job has finished
    # Returns:
    #	$number_of_bytes transferred in return
    my $self = shift;
    for my $file ($self->return()) {
	if(-e $file) {
	    $self->{'returnsize'} += (stat($file))[7];
	}
    }
    return $self->{'returnsize'};
}

sub add_returnsize($) {
    my $self = shift;
    my $returnsize = shift;
    $self->{'returnsize'} += $returnsize;
    $opt::sqlworker and
	$Global::sql->update("SET Receive = ? WHERE Seq = ".$self->seq(),
			     $self->{'returnsize'});
}

sub sshreturn($) {
    # Returns for each return-file:
    #	rsync remote:$workdir/$file .
    my $self = shift;
    my $sshlogin = $self->sshlogin();
    my $pre = "";
    for my $file ($self->return()) {
	$file =~ s:^\./::g; # Remove ./ if any
	my $relpath = ($file !~ m:^/:) ||
	    ($file =~ m:/\./:); # Is the path relative or /./?
	my $cd = "";
	my $wd = "";
	if($relpath) {
	    #	rsync -avR /foo/./bar/baz.c remote:/tmp/
	    # == (on old systems)
	    #	rsync -avR --rsync-path="cd /foo; rsync" remote:bar/baz.c /tmp/
	    $wd = ::shell_quote_file($self->workdir()."/");
	}
	# Only load File::Basename if actually needed
	$Global::use{"File::Basename"} ||= eval "use File::Basename; 1;";
	# dir/./file means relative to dir, so remove dir on remote
	$file =~ m:(.*)/\./:;
	my $basedir = $1 ? ::shell_quote_file($1."/") : "";
	my $nobasedir = $file;
	$nobasedir =~ s:.*/\./::;
	$cd = ::shell_quote_file(::dirname($nobasedir));
	my $rsync_cd = '--rsync-path='.::Q("cd $wd$cd; rsync");
	my $basename = ::Q(::shell_quote_file(::basename($file)));
	# --return
	#   mkdir -p /home/tange/dir/subdir/;
	#   rsync (--protocol 30) -rlDzR
	#     --rsync-path="cd /home/tange/dir/subdir/; rsync"
	#     server:file.gz /home/tange/dir/subdir/
	$pre .= "mkdir -p $basedir$cd" . " && " .
	    $sshlogin->rsync(). " $rsync_cd -- ".$sshlogin->host().':'.
	    $basename . " ".$basedir.$cd.";";
    }
    return $pre;
}

sub sshcleanup($) {
    # Return the sshcommand needed to remove the file
    # Returns:
    #	ssh command needed to remove files from sshlogin
    my $self = shift;
    my $sshlogin = $self->sshlogin();
    my $workdir = $self->workdir();
    my $cleancmd = "";

    for my $file ($self->remote_cleanup()) {
	my @subworkdirs = parentdirs_of($file);
	$cleancmd .= $sshlogin->cleanup_cmd($file,$workdir).";";
    }
    if(defined $opt::workdir and $opt::workdir eq "...") {
	$cleancmd .= $sshlogin->wrap("rm -rf " . ::Q($workdir).';');
    }
    return $cleancmd;
}

sub remote_cleanup($) {
    # Returns:
    #	Files to remove at cleanup
    my $self = shift;
    if($opt::cleanup) {
	my @transfer = $self->transfer();
	my @return = $self->return();
	return (@transfer,@return);
    } else {
	return ();
    }
}

sub exitstatuswrapper(@) {
    # Input:
    #	@shellcode = shell code to execute
    # Returns:
    #	shell script that returns current status after executing @shellcode
    if($Global::cshell) {
	return ('set _EXIT_status=$status; ' .
		join(" ",@_).
		'exit $_EXIT_status;');
    } elsif($Global::fish) {
	return ('export _EXIT_status=$status; ' .
		join(" ",@_).
		'exit $_EXIT_status;');
    } else {
	return ('_EXIT_status=$?; ' .
		join(" ",@_).
		'exit $_EXIT_status;');
    }
}

sub workdir($) {
    # Returns:
    #	the workdir on a remote machine
    my $self = shift;
    if(not defined $self->{'workdir'}) {
	my $workdir;
	if(defined $opt::workdir) {
	    if($opt::workdir eq ".") {
		# . means current dir
		my $home = $ENV{'HOME'};
		eval 'use Cwd';
		my $cwd = cwd();
		$workdir = $cwd;
		if($home) {
		    # If homedir exists: remove the homedir from
		    # workdir if cwd starts with homedir
		    # E.g. /home/foo/my/dir => my/dir
		    # E.g. /tmp/my/dir => /tmp/my/dir
		    my ($home_dev, $home_ino) = (stat($home))[0,1];
		    my $parent = "";
		    my @dir_parts = split(m:/:,$cwd);
		    my $part;
		    while(defined ($part = shift @dir_parts)) {
			$part eq "" and next;
			$parent .= "/".$part;
			my ($parent_dev, $parent_ino) = (stat($parent))[0,1];
			if($parent_dev == $home_dev and $parent_ino == $home_ino) {
			    # dev and ino is the same: We found the homedir.
			    $workdir = join("/",@dir_parts);
			    last;
			}
		    }
		}
		if($workdir eq "") {
		    $workdir = ".";
		}
	    } elsif($opt::workdir eq "...") {
		$workdir = ".parallel/tmp/" . ::hostname() . "-" . $$
		    . "-" . $self->seq();
	    } else {
		$workdir = $self->{'commandline'}->
		    replace_placeholders([$opt::workdir],0,0);
		#$workdir = $opt::workdir;
		# Rsync treats /./ special. We dont want that
		$workdir =~ s:/\./:/:g; # Remove /./
		$workdir =~ s:(.)/+$:$1:; # Remove ending / if any
		$workdir =~ s:^\./::g; # Remove starting ./ if any
	    }
	} else {
	    $workdir = ".";
	}
	$self->{'workdir'} = $workdir;
    }
    return $self->{'workdir'};
}

sub parentdirs_of($) {
    # Return:
    #	all parentdirs except . of this dir or file - sorted desc by length
    my $d = shift;
    my @parents = ();
    while($d =~ s:/[^/]+$::) {
	if($d ne ".") {
	    push @parents, $d;
	}
    }
    return @parents;
}

sub start($) {
    # Setup STDOUT and STDERR for a job and start it.
    # Returns:
    #	job-object or undef if job not to run

    sub open3_setpgrp_internal {
	# Run open3+setpgrp followed by the command
	# Input:
	#   $stdin_fh = Filehandle to use as STDIN
	#   $stdout_fh = Filehandle to use as STDOUT
	#   $stderr_fh = Filehandle to use as STDERR
	#   $command = Command to run
	# Returns:
	#   $pid = Process group of job started
	my ($stdin_fh,$stdout_fh,$stderr_fh,$command) = @_;
	my $pid;
	local (*OUT,*ERR);
	open OUT, '>&', $stdout_fh or ::die_bug("Can't dup STDOUT: $!");
	open ERR, '>&', $stderr_fh or ::die_bug("Can't dup STDERR: $!");
	# The eval is needed to catch exception from open3
	eval {
	    if(not $pid = ::open3($stdin_fh, ">&OUT", ">&ERR", "-")) {
		# Each child gets its own process group to make it safe to killall
		eval{ setpgrp(0,0) };
		eval{ setpriority(0,0,$opt::nice) };
		exec($Global::shell,"-c",$command)
		    || ::die_bug("open3-$stdin_fh ".substr($command,0,200));
	    }
	};
	return $pid;
    }

    sub open3_setpgrp_external {
	# Run open3 on $command wrapped with a perl script doing setpgrp
	# Works on systems that do not support open3(,,,"-")
	# Input:
	#   $stdin_fh = Filehandle to use as STDIN
	#   $stdout_fh = Filehandle to use as STDOUT
	#   $stderr_fh = Filehandle to use as STDERR
	#   $command = Command to run
	# Returns:
	#   $pid = Process group of job started
	my ($stdin_fh,$stdout_fh,$stderr_fh,$command) = @_;
	local (*OUT,*ERR);
	open OUT, '>&', $stdout_fh or ::die_bug("Can't dup STDOUT: $!");
	open ERR, '>&', $stderr_fh or ::die_bug("Can't dup STDERR: $!");

	my $pid;
	my @setpgrp_wrap =
	    ('perl','-e',
	     "eval\{setpgrp\}\;eval\{setpriority\(0,0,$opt::nice\)\}\;".
	     "exec '$Global::shell', '-c', \@ARGV");
	# The eval is needed to catch exception from open3
	eval {
	    $pid = ::open3($stdin_fh, ">&OUT", ">&ERR", @setpgrp_wrap, $command)
		|| ::die_bug("open3-$stdin_fh");
	    1;
	};
	return $pid;
    }

    sub redefine_open3_setpgrp {
	my $setgprp_cache = shift;
	# Select and run open3_setpgrp_internal/open3_setpgrp_external
	no warnings 'redefine';
	my ($outfh,$name) = ::tmpfile(SUFFIX => ".tst");
	# Test to see if open3(x,x,x,"-") is fully supported
	# Can an exported bash function be called via open3?
	my $script = 'if($pid=::open3($i,$o,$e,"-")) { wait; } '.
	    'else { exec("bash","-c","testfun && true"); }';
	my $bash =
	    ::shell_quote_scalar_default(
	    "testfun() { rm $name; }; export -f testfun; ".
	    "perl -MIPC::Open3 -e ".
	    ::Q(::Q($script))
	    );
	my $redefine_eval;
	# Redirect STDERR temporarily,
	# so errors on MacOS X are ignored.
	open my $saveerr, ">&STDERR";
	open STDERR, '>', "/dev/null";
	# Run the test
	::debug("init",qq{bash -c $bash 2>/dev/null});
	qx{ bash -c $bash 2>/dev/null };
	open STDERR, ">&", $saveerr;

	if(-e $name) {
	    # Does not support open3(x,x,x,"-")
	    # or does not have bash:
	    # Use (slow) external version
	    unlink($name);
	    $redefine_eval = '*open3_setpgrp = \&open3_setpgrp_external';
	    ::debug("init","open3_setpgrp_external chosen\n");
	} else {
	    # Supports open3(x,x,x,"-")
	    # This is 0.5 ms faster to run
	    $redefine_eval = '*open3_setpgrp = \&open3_setpgrp_internal';
	    ::debug("init","open3_setpgrp_internal chosen\n");
	}
	if(open(my $fh, ">", $setgprp_cache)) {
	    print $fh $redefine_eval;
	    close $fh;
	} else {
	    ::debug("init","Cannot write to $setgprp_cache");
	}
	eval $redefine_eval;
    }

    sub open3_setpgrp {
	my $setgprp_cache = $Global::cache_dir . "/tmp/sshlogin/" .
	    ::hostname() . "/setpgrp_func";
	sub read_cache() {
	    -e $setgprp_cache || return 0;
	    local $/ = undef;
	    open(my $fh, "<", $setgprp_cache) || return 0;
	    eval <$fh> || return 0;
	    close $fh;
	    return 1;
	}
	if(not read_cache()) {
	    redefine_open3_setpgrp($setgprp_cache);
	}
	# The sub is now redefined. Call it
	return open3_setpgrp(@_);
    }

    my $job = shift;
    # Get the shell command to be executed (possibly with ssh infront).
    my $command = $job->wrapped();
    my $pid;

    if($Global::interactive or $Global::stderr_verbose) {
	$job->interactive_start();
    }
    # Must be run after $job->interactive_start():
    # $job->interactive_start() may call $job->skip()
    if($job->{'commandline'}{'skip'}
       or
       not $job->filter()) {
	# $job->skip() was called or job filtered
	$command = "true";
    }
    $job->openoutputfiles();
    $job->print_verbose_dryrun();
    my($stdout_fh,$stderr_fh) = ($job->fh(1,"w"),$job->fh(2,"w"));
    if($opt::dryrun or $opt::sqlmaster) { $command = "true"; }
    $ENV{'PARALLEL_SEQ'} = $job->seq();
    $ENV{'PARALLEL_PID'} = $$;
    $ENV{$opt::process_slot_var} = -1 +
	($ENV{'PARALLEL_JOBSLOT'} = $job->slot());
    $ENV{'PARALLEL_TMP'} = ::tmpname("par");
    $job->add_rm($ENV{'PARALLEL_TMP'});
    $job->fill_templates();
    $ENV{'SSHPASS'} = $job->{'sshlogin'}->{'password'};
    ::debug("run", $Global::total_running, " processes . Starting (",
	    $job->seq(), "): $command\n");
    if($opt::pipe) {
	my ($stdin_fh) = ::gensym();
	$pid = open3_setpgrp($stdin_fh,$stdout_fh,$stderr_fh,$command);
	if($opt::roundrobin and not $opt::keeporder) {
	    # --keep-order will make sure the order will be reproducible
	    ::set_fh_non_blocking($stdin_fh);
	}
	$job->set_fh(0,"w",$stdin_fh);
	if($opt::tee or $opt::shard or $opt::bin) { $job->set_virgin(0); }
    } elsif(($opt::tty or $opt::open_tty) and -c "/dev/tty" and
	    open(my $devtty_fh, "<", "/dev/tty")) {
	# Give /dev/tty to the command if no one else is using it
	# The eval is needed to catch exception from open3
	local (*IN,*OUT,*ERR);
	open OUT, '>&', $stdout_fh or ::die_bug("Can't dup STDOUT: $!");
	open ERR, '>&', $stderr_fh or ::die_bug("Can't dup STDERR: $!");
	*IN = $devtty_fh;
	# The eval is needed to catch exception from open3
	my @wrap = ('perl','-e',
			    "eval\{setpriority\(0,0,$opt::nice\)\}\;".
			    "exec '$Global::shell', '-c', \@ARGV");
	eval {
	    $pid = ::open3("<&IN", ">&OUT", ">&ERR", @wrap, $command)
		|| ::die_bug("open3-/dev/tty");
	    1;
	};
	close $devtty_fh;
	$job->set_virgin(0);
    } elsif($Global::semaphore) {
	# Allow sem to read from stdin
	$pid = open3_setpgrp("<&STDIN",$stdout_fh,$stderr_fh,$command);
	$job->set_virgin(0);
    } else {
	$pid = open3_setpgrp(::gensym(),$stdout_fh,$stderr_fh,$command);
	$job->set_virgin(0);
    }
    if($pid) {
	# A job was started
	$Global::total_running++;
	$Global::total_started++;
	$job->set_pid($pid);
	$job->set_starttime();
	$Global::running{$job->pid()} = $job;
	if($opt::timeout) {
	    $Global::timeoutq->insert($job);
	}
	$Global::newest_job = $job;
	$Global::newest_starttime = ::now();
	return $job;
    } else {
	# No more processes
	::debug("run", "Cannot spawn more jobs.\n");
	return undef;
    }
}

sub interactive_start($) {
    my $self = shift;
    my $command = $self->wrapped();
    if($Global::interactive) {
	my $answer;
	::status_no_nl("$command ?...");
	do{
	    open(my $tty_fh, "<", "/dev/tty") || ::die_bug("interactive-tty");
	    $answer = <$tty_fh>;
	    close $tty_fh;
	    # Sometime we get an empty string (not even \n)
	    # Do not know why, so let us just ignore it and try again
	} while(length $answer < 1);
	if (not ($answer =~ /^\s*y/i)) {
	    $self->{'commandline'}->skip();
	}
    } else {
	print $Global::original_stderr "$command\n";
    }
}

{
    my $tmuxsocket;
    my $qsocket;

    sub tmux_wrap($) {
	# Wrap command with tmux for session pPID
	# Input:
	#   $actual_command = the actual command being run (incl ssh wrap)
	my $self = shift;
	my $actual_command = shift;
	# Temporary file name. Used for fifo to communicate exit val
	my $tmpfifo = ::tmpname("tmx");
	$self->add_rm($tmpfifo);
	if(length($tmpfifo) >=100) {
	    ::error("tmux does not support sockets with path > 100.");
	    ::wait_and_exit(255);
	}
	if($opt::tmuxpane) {
	    # Move the command into a pane in window 0
	    $actual_command = $ENV{'PARALLEL_TMUX'}.' joinp -t :0 ; '.
		$ENV{'PARALLEL_TMUX'}.' select-layout -t :0 tiled ; '.
		$actual_command;
	}
	my $visual_command = $self->replaced();
	my $title = $visual_command;
	if($visual_command =~ /\0/) {
	    ::error("Command line contains NUL. tmux is confused by NUL.");
	    ::wait_and_exit(255);
	}
	# ; causes problems
	# ascii 194-245 annoys tmux
	$title =~ tr/[\011-\016;\302-\365]/ /s;
	$title = ::Q($title);

	my $l_act = length($actual_command);
	my $l_tit = length($title);
	my $l_fifo = length($tmpfifo);
	# The line to run contains a 118 chars extra code + the title 2x
	my $l_tot = 2 * $l_tit + $l_act + $l_fifo;

	my $quoted_space75 = ::Q(" ")x75;
	while($l_tit < 1000 and
	      (
	       (890 < $l_tot and $l_tot < 1350)
	       or
	       (9250 < $l_tot and $l_tot < 9800)
	      )) {
	    # tmux blocks for certain lengths:
	    # 900 < title + command < 1200
	    # 9250 < title + command < 9800
	    # but only if title < 1000, so expand the title with 75 spaces
	    # The measured lengths are:
	    # 996 < (title + whole command) < 1127
	    # 9331 < (title + whole command) < 9636
	    $title .= $quoted_space75;
	    $l_tit = length($title);
	    $l_tot = 2 * $l_tit + $l_act + $l_fifo;
	}

	my $tmux;
	$ENV{'PARALLEL_TMUX'} ||= "tmux";
	if(not $tmuxsocket) {
	    $tmuxsocket = ::tmpname("tms");
	    $qsocket = ::Q($tmuxsocket);
	    ::debug("tmux", "Start: $ENV{'PARALLEL_TMUX'} -S $qsocket attach");
	    if($opt::fg) {
		if(not fork) {
		    # Run tmux in the foreground
		    # Wait for the socket to appear
		    while (not -e $tmuxsocket) { }
		    `$ENV{'PARALLEL_TMUX'} -S $qsocket attach`;
		    exit;
		}
	    }
	    ::status("See output with: $ENV{'PARALLEL_TMUX'} -S $qsocket attach");
	}
	$tmux = "sh -c ".::Q(
	    $ENV{'PARALLEL_TMUX'}.
	    " -S $qsocket new-session -s p$$ -d \"sleep .2\" >/dev/null 2>&1").";" .
	    $ENV{'PARALLEL_TMUX'}.
	    " -S $qsocket new-window -t p$$ -n $title";

	::debug("tmux", "title len:", $l_tit, " act ", $l_act, " max ",
		$Limits::Command::line_max_len, " tot ",
		$l_tot, "\n");
	return "mkfifo ".::Q($tmpfifo)." && $tmux ".
	    # Run in tmux
	    ::Q
	    (
	     "(".$actual_command.');'.
	     # The triple print is needed - otherwise the testsuite fails
	     q[ perl -e 'while($t++<3){ print $ARGV[0],"\n" }' $?h/$status >> ].
	     ::Q($tmpfifo)."&".
	     "echo $title; echo \007Job finished at: `date`;sleep 10"
	    ).
	    # Run outside tmux
	    # Read a / separated line: 0h/2 for csh, 2/0 for bash.
	    # If csh the first will be 0h, so use the second as exit value.
	    # Otherwise just use the first value as exit value.
	    q{; exec perl -e '$/="/";$_=<>;$c=<>;unlink $ARGV; }.
	    q{/(\d+)h/ and exit($1);exit$c' }.::Q($tmpfifo);
    }
}

sub is_already_in_results($) {
    # Do we already have results for this job?
    # Returns:
    #	$job_already_run = bool whether there is output for this or not
    my $job = $_[0];
    if($Global::csvsep) {
	if($opt::joblog) {
	    # OK: You can look for job run in joblog
	    return 0
	} else {
	    ::warning_once(
		  "--resume --results .csv/.tsv/.json is not supported yet\n");
	    # TODO read and parse the file
	    return 0
	}
    }
    my $out = $job->{'commandline'}->results_out();
    ::debug("run", "Test ${out}stdout", -e "${out}stdout", "\n");
    return(-e $out."stdout" or -f $out);
}

sub is_already_in_joblog($) {
    my $job = shift;
    return vec($Global::job_already_run,$job->seq(),1);
}

sub set_job_in_joblog($) {
    my $job = shift;
    vec($Global::job_already_run,$job->seq(),1) = 1;
}

sub should_be_retried($) {
    # Should this job be retried?
    # Returns
    #	0 - do not retry
    #	1 - job queued for retry
    my $self = shift;
    if (not defined $opt::retries) { return 0; }
    if(not $self->exitstatus() and not $self->exitsignal()) {
	# Completed with success. If there is a recorded failure: forget it
	$self->reset_failed_here();
	return 0;
    } else {
	# The job failed. Should it be retried?
	$self->add_failed_here();
	my $retries = $self->{'commandline'}->
	    replace_placeholders([$opt::retries],0,0);
	# 0 = Inf
	if($retries == 0) { $retries = 2**31; }
	# Ignore files already unlinked to avoid memory leak
	$self->{'unlink'} = [ grep { -e $_ } @{$self->{'unlink'}} ];
	map { -e $_ or delete $Global::unlink{$_} } keys %Global::unlink;
	if($self->total_failed() == $retries) {
	    # This has been retried enough
	    return 0;
	} else {
	    # This command should be retried
	    $self->set_endtime(undef);
	    $self->reset_exitstatus();
	    $Global::JobQueue->unget($self);
	    ::debug("run", "Retry ", $self->seq(), "\n");
	    return 1;
	}
    }
}

{
    my (%print_later,$job_seq_to_print);

    sub print_earlier_jobs($) {
	# Print jobs whose output is postponed due to --keep-order
	# Returns: N/A
	my $job = shift;
	$print_later{$job->seq()} = $job;
	$job_seq_to_print ||= 1;
	my $returnsize = 0;
	::debug("run", "Looking for: $job_seq_to_print ",
		"This: ", $job->seq(), "\n");
	for(;vec($Global::job_already_run,$job_seq_to_print,1);
	    $job_seq_to_print++) {}
	while(my $j = $print_later{$job_seq_to_print}) {
	    $returnsize += $j->print();
	    if($j->endtime()) {
		# Job finished - look at the next
		delete $print_later{$job_seq_to_print};
		$job_seq_to_print++;
		next;
	    } else {
		# Job not finished yet - look at it again next round
		last;
	    }
	}
	return $returnsize;
    }
}

sub print($) {
    # Print the output of the jobs
    # Returns: N/A
    my $self = shift;

    ::debug("print", ">>joboutput ", $self->replaced(), "\n");
    if($opt::dryrun) {
	# Nothing was printed to this job:
	# cleanup tmp files if --files was set
	::rm($self->fh(1,"name"));
    }
    if($opt::pipe and $self->virgin() and not $opt::tee) {
	# Skip --joblog, --dryrun, --verbose
    } else {
	if($opt::ungroup) {
	    # NULL returnsize = 0 returnsize
	    $self->returnsize() or $self->add_returnsize(0);
	    if($Global::joblog and defined $self->{'exitstatus'}) {
		# Add to joblog when finished
		$self->print_joblog();
		# Printing is only relevant for grouped/--line-buffer output.
		$opt::ungroup and return;
	    }
	}
	# Check for disk full
	::exit_if_disk_full();
    }

    my $returnsize = $self->returnsize();
    my @fdno;
    if($opt::latestline) {
	@fdno = (1);
    } else {
	@fdno = (sort { $a <=> $b } keys %Global::fh);
    }
    for my $fdno (@fdno) {
	# Sort by file descriptor numerically: 1,2,3,..,9,10,11
	$fdno == 0 and next;
	my $out_fh = $Global::fh{$fdno};
	my $in_fh = $self->fh($fdno,"r");
	if(not $in_fh) {
	    if(not $Job::file_descriptor_warning_printed{$fdno}++) {
		# ::warning("File descriptor $fdno not defined\n");
	    }
	    next;
	}
	::debug("print", "File descriptor $fdno (", $self->fh($fdno,"name"), "):\n");
	if($Global::linebuffer) {
	    # Line buffered print out
	    $self->print_linebuffer($fdno,$in_fh,$out_fh);
	} elsif($Global::files) {
	    $self->print_files($fdno,$in_fh,$out_fh);
	} elsif($opt::results) {
	    $self->print_results($fdno,$in_fh,$out_fh);
	} else {
	    $self->print_normal($fdno,$in_fh,$out_fh);
	}
	flush $out_fh;
    }
    ::debug("print", "<<joboutput\n");
    if(defined $self->{'exitstatus'}
       and not ($self->virgin() and $opt::pipe)) {
	if($Global::joblog and not $opt::sqlworker) {
	    # Add to joblog when finished
	    $self->print_joblog();
	}
	if($opt::sqlworker and not $opt::results) {
	    $Global::sql->output($self);
	}
	if($Global::csvsep) {
	    # Add output to CSV when finished
	    $self->print_csv();
	}
	if($Global::jsonout) {
	    $self->print_json();
	}
    }
    return $returnsize - $self->returnsize();
}

{
    my %jsonmap;

    sub print_json($) {
	my $self = shift;
	sub jsonquote($) {
	    my $a = shift;
	    if(not $jsonmap{"\001"}) {
		map { $jsonmap{sprintf("%c",$_)} =
			  sprintf '\u%04x', $_ } 0..31;
	    }
	    $a =~ s/\\/\\\\/g;
	    $a =~ s/\"/\\"/g;
	    $a =~ s/([\000-\037])/$jsonmap{$1}/g;
	    return $a;
	}

	my $cmd;
	if($Global::verbose <= 1) {
	    $cmd = jsonquote($self->replaced());
	} else {
	    # Verbose level > 1: Print the rsync and stuff
	    $cmd = jsonquote(join " ", @{$self->{'commandline'}});
	}
	my $record_ref = $self->{'commandline'}{'arg_list_flat_orig'};

	# Memory optimization: Overwrite with the joined output
	$self->{'output'}{1} = join("", @{$self->{'output'}{1}});
	$self->{'output'}{2} = join("", @{$self->{'output'}{2}});
	# {
	#   "Seq": 12,
	#   "Host": "/usr/bin/ssh foo@lo",
	#   "Starttime": 1608344711.743,
	#   "JobRuntime": 0.01,
	#   "Send": 0,
	#   "Receive": 10,
	#   "Exitval": 0,
	#   "Signal": 0,
	#   "Command": "echo 1",
	#   "V": [
	#     "1"
	#   ],
	#   "Stdout": "1\n",
	#   "Stderr": ""
	# }
	#
	printf($Global::csv_fh
	       q({ "Seq": %s, "Host": "%s", "Starttime": %s, "JobRuntime": %s, ).
	       q("Send": %s, "Receive": %s, "Exitval": %s, "Signal": %s, ).
	       q("Command": "%s", "V": [ %s ], "Stdout": "%s", "Stderr": "%s" }).
	       "\n",
	       $self->seq(),
	       jsonquote($self->sshlogin()->string()),
	       $self->starttime(), sprintf("%0.3f",$self->runtime()),
	       $self->transfersize(), $self->returnsize(),
	       $self->exitstatus(), $self->exitsignal(), $cmd,
	       (join ",",
		map { '"'.jsonquote($_).'"' } @$record_ref[1..$#$record_ref],
	       ),
	       jsonquote($self->{'output'}{1}),
	       jsonquote($self->{'output'}{2})
	    );
    }
}

{
    my $header_printed;

    sub print_csv($) {
	my $self = shift;
	my $cmd;
	if($Global::verbose <= 1) {
	    $cmd = $self->replaced();
	} else {
	    # Verbose level > 1: Print the rsync and stuff
	    $cmd = join " ", @{$self->{'commandline'}};
	}
	my $record_ref = $self->{'commandline'}{'arg_list_flat_orig'};

	if(not $header_printed) {
	    # Variable headers
	    # Normal => V1..Vn
	    # --header : => first value from column
	    my @V;
	    if($opt::header) {
		my $i = 1;
		@V = (map { $Global::input_source_header{$i++} }
		      @$record_ref[1..$#$record_ref]);
	    } else {
		my $V = "V1";
		@V = (map { $V++ } @$record_ref[1..$#$record_ref]);
	    }
	    print $Global::csv_fh
		(map { $$_ }
		 combine_ref("Seq", "Host", "Starttime", "JobRuntime",
			     "Send", "Receive", "Exitval", "Signal", "Command",
			     @V,
			     "Stdout","Stderr"
		 )),"\n";
	    $header_printed++;
	}
	# Memory optimization: Overwrite with the joined output
	$self->{'output'}{1} = join("", @{$self->{'output'}{1}});
	$self->{'output'}{2} = join("", @{$self->{'output'}{2}});
	print $Global::csv_fh
	    (map { $$_ }
	     combine_ref
	     ($self->seq(),
	      $self->sshlogin()->string(),
	      $self->starttime(), sprintf("%0.3f",$self->runtime()),
	      $self->transfersize(), $self->returnsize(),
	      $self->exitstatus(), $self->exitsignal(), \$cmd,
	      \@$record_ref[1..$#$record_ref],
	      \$self->{'output'}{1},
	      \$self->{'output'}{2})),"\n";
    }
}

sub combine_ref($) {
    # Inspired by Text::CSV_PP::_combine (by Makamaka Hannyaharamitu)
    my @part = @_;
    my $sep = $Global::csvsep;
    my $quot = '"';
    my @out = ();

    my $must_be_quoted;
    for my $column (@part) {
	# Memory optimization: Content transferred as reference
	if(ref $column ne "SCALAR") {
	    # Convert all columns to scalar references
	    my $v = $column;
	    $column = \$v;
	}
	if(not defined $$column) {
	    $$column = '';
	    next;
	}

	$must_be_quoted = 0;

	if($$column =~ s/$quot/$quot$quot/go){
	    # Replace " => ""
	    $must_be_quoted ||=1;
	}
	if($$column =~ /[\s\Q$sep\E]/o){
	    # Put quotes around if the column contains ,
	    $must_be_quoted ||=1;
	}

	$Global::use{"bytes"} ||= eval "use bytes; 1;";
	if ($$column =~ /\0/) {
	    # Contains \0 => put quotes around
	    $must_be_quoted ||=1;
	}
	if($must_be_quoted){
	    push @out, \$sep, \$quot, $column, \$quot;
	} else {
	    push @out, \$sep, $column;
	}
    }
    # Remove the first $sep: ,val,"val" => val,"val"
    shift @out;
    return @out;
}

sub print_files($) {
    # Print the name of the file containing stdout on stdout
    # Uses:
    #	$opt::pipe
    #	$opt::group = Print when job is done
    #	$opt::linebuffer = Print ASAP
    # Returns: N/A
    my $self = shift;
    my ($fdno,$in_fh,$out_fh) = @_;

    # If the job is dead: close printing fh. Needed for --compress
    close $self->fh($fdno,"w");
    if($? and $opt::compress) {
	::error($opt::compress_program." failed.");
	$self->set_exitstatus(255);
    }
    if($opt::compress) {
	# Kill the decompressor which will not be needed
	CORE::kill "TERM", $self->fh($fdno,"rpid");
    }
    close $in_fh;

    if($opt::pipe and $self->virgin()) {
	# Nothing was printed to this job:
	# cleanup unused tmp files because --files was set
	for my $fdno (1,2) {
	    ::rm($self->fh($fdno,"name"));
	    ::rm($self->fh($fdno,"unlink"));
	}
    } elsif($fdno == 1 and $self->fh($fdno,"name")) {
	print $out_fh $self->tag(),$self->fh($fdno,"name"), $Global::files_sep;
	if($Global::membuffer) {
	    push @{$self->{'output'}{$fdno}},
		$self->tag(), $self->fh($fdno,"name");
	}
	$self->add_returnsize(-s $self->fh($fdno,"name"));
	# Mark as printed - do not print again
	$self->set_fh($fdno,"name",undef);
    }
}


# Different print types
# (--ll | --ll --bar | --lb | --group | --parset | --sql-worker)
# (--files | --results (.json|.csv|.tsv) )
# --color-failed
# --color
# --keep-order
# --tag
# --bar
{
    my ($up,$eol,$currow,$maxrow);
    my ($minvisible,%print_later,%notvisible);
    my (%binmodeset,%tab);

    sub latestline_init() {
	# cursor_up cuu1 = up one line
	$up = `sh -c "tput cuu1 </dev/tty" 2>/dev/null`;
	chomp($up);
	$eol = `sh -c "tput el </dev/tty" 2>/dev/null`;
	chomp($eol);
	if($eol eq "") { $eol = "\033[K"; }
	$currow = 1;
	$maxrow = 1;
	$minvisible = 1;
	for(0..8) {
	    $tab{$_} = " "x(8-($_%8));
	}
    }

    sub mbtrunc($$) {
	# Simple mbtrunc to avoid using Text::WideChar::Util
	my $str = shift;
	my $len = shift;
	if(::mbswidth($str) == length($str)) {
	    $str = substr($str,0,$len);
	} else {
	    # mb chars (ヌー平行) are wider than 1 char on screen
	    # We need at most $len chars - they may be wide
	    $str =~ s/(.{$len}).*/$1/;
	    my $rlen = int((::mbswidth($str) - $len)/2+0.5);
	    do {
		$str =~ s/.{$rlen}$//;
		$rlen = int((::mbswidth($str) - $len)/2+0.5);
	    } while($rlen >= 1);
	}
	return $str;
    }

    sub print_latest_line($) {
	my $self = shift;
	my $out_fh = shift;
	if(not defined $self->{$out_fh,'latestline'}) { return; }
	my $row = $self->row();
	# Is row visible?
	if(not ($minvisible <= $row
		and
		$row < $minvisible + ::terminal_rows() - 1)) {
	    return;
	}
	if(not $binmodeset{$out_fh}++) {
	    # Enable utf8 if possible
	    eval q{ binmode $out_fh, "encoding(utf8)"; };
	}
	my ($color,$reset_color) = $self->color();
	my $termcol = ::terminal_columns();
	my $untabify_tag = ::decode_utf8($self->untabtag());
	my $untabify_str =
	    ::untabify(::decode_utf8($self->{$out_fh,'latestline'}));
	# -1 to make space for $truncated_str
	my $maxtaglen = $termcol - 1;
	$untabify_tag = mbtrunc($untabify_tag,$maxtaglen);
	my $taglen = ::mbswidth($untabify_tag);
	my $maxstrlen = $termcol - $taglen - 1;
	$untabify_str = mbtrunc($untabify_str,$maxstrlen);
	my $strlen = ::mbswidth($untabify_str);
	my $truncated_tag = "";
	my $truncated_str = "";
	if($termcol - $taglen < 2) {
	    $truncated_tag = ">";
	} else {
	    if($termcol - $taglen - $strlen <= 2) {
		$truncated_str = ">";
	    }
	}
	$maxrow = ($row > $maxrow) ? $row : $maxrow;
	printf($out_fh
	       ("%s%s%s%s". # up down \r eol
		"%s%s". # tag trunc_tag
		"%s%s%s%s". # color line trunc reset_color
		"%s" # down
	       ),
	       "$up"x($currow - $row), "\n"x($row - $currow), "\r", $eol,
	       $untabify_tag,$truncated_tag,
	       $color, $untabify_str, $truncated_str, $reset_color,
	       "\n"x($maxrow - $row + 1));
	$currow = $maxrow + 1;
    }

    sub print_linebuffer($) {
	my $self = shift;
	my ($fdno,$in_fh,$out_fh) = @_;
	if(defined $self->{'exitstatus'}) {
	    # If the job is dead: close printing fh. Needed for --compress
	    close $self->fh($fdno,"w");
	    if($opt::compress) {
		if($?) {
		    ::error($opt::compress_program." failed.");
		    $self->set_exitstatus(255);
		}
		# Blocked reading in final round
		for my $fdno (1,2) { ::set_fh_blocking($self->fh($fdno,'r')); }
	    }
	    if($opt::latestline) { $print_later{$self->row()} = $self; }
	}
	if(not $self->virgin()) {
	    if($Global::files or ($opt::results and not $Global::csvsep)) {
		# Print filename
		if($fdno == 1 and not $self->fh($fdno,"printed")) {
		    print $out_fh $self->tag(),$self->fh($fdno,"name"),"\n";
		    if($Global::membuffer) {
			push(@{$self->{'output'}{$fdno}}, $self->tag(),
			     $self->fh($fdno,"name"));
		    }
		    $self->set_fh($fdno,"printed",1);
		}
		# No need for reading $in_fh, as it is from "cat >/dev/null"
	    } else {
		# Read halflines and print full lines
		my $outputlength = 0;
		my $halfline_ref = $self->{'halfline'}{$fdno};
		my ($buf,$i,$rv);
		# 1310720 gives 1.2 GB/s
		# 131072  gives 0.9 GB/s
		# The optimal block size differs
		# It has been measured on:
		# AMD 6376: 60800 (>70k is also reasonable)
		# Intel i7-3632QM: 52-59k, 170-175k
		# seq 64 | ppar --_test $1 --lb \
		#   'yes {} `seq 1000`|head -c 10000000' >/dev/null
		while($rv = sysread($in_fh, $buf, 60800)) {
		    $outputlength += $rv;
		    # TODO --recend
		    # Treat both \n and \r as line end
		    # Only test for \r if there is no \n
		    # Test:
		    #   perl -e '$a="x"x1000000;
		    #	     $b="$a\r$a\n$a\r$a\n";
		    #	     map { print $b,$_ } 1..10'
		    $i = ((rindex($buf,"\n")+1) || (rindex($buf,"\r")+1));
		    if($i) {
			if($opt::latestline) {
			    # Keep the latest full line
			    my $l = join('', @$halfline_ref,
					 substr($buf,0,$i-1));
			    # "ab\rb\n" = "bb", but we cannot process that correctly.
			    # Line may be:
			    #    foo \r bar \n
			    #    foo \r bar \r baz \r
			    # If so: Remove 'foo \r'
			    $l =~ s/.*\r//g;
			    my $j = ((rindex($l,"\n")+1) ||
				     (rindex($l,"\r")+1));
			    $self->{$out_fh,'latestline'} = substr($l,$j);
			    # Remove the processed part
			    # by keeping the unprocessed part
			    @$halfline_ref = (substr($buf,$i));
			} else {
			    # One or more complete lines were found
			    if($Global::color) {
				my $print = join("",@$halfline_ref,
						 substr($buf,0,$i));
				chomp($print);
				my ($color,$reset_color) = $self->color();
				my $colortag = $color.$self->tag();
				# \n => reset \n color tag
				$print =~ s{([\n\r])(?=.|$)}
				{$reset_color$1$colortag}gs;
				print($out_fh $colortag, $print,
				      $reset_color, "\n");
			    } elsif($opt::tag or defined $opt::tagstring) {
				# Replace ^ with $tag within the full line
				if($Global::cache_replacement_eval) {
				    # Replace with the same value for tag
				    my $tag = $self->tag();
				    unshift @$halfline_ref, $tag;
				    # TODO --recend that can be partially in
				    # @$halfline_ref
				    substr($buf,0,$i-1) =~
					s/([\n\r])(?=.|$)/$1$tag/gs;
				} else {
				    # Replace with freshly computed tag-value
				    unshift @$halfline_ref, $self->tag();
				    substr($buf,0,$i-1) =~
					s/([\n\r])(?=.|$)/$1.$self->tag()/gse;
				}
				# The length changed,
				# so find the new ending pos
				$i = ::max((rindex($buf,"\n")+1),
					   (rindex($buf,"\r")+1));
				# Print the partial line (halfline)
				# and the last half
				print $out_fh @$halfline_ref, substr($buf,0,$i);
			    } else {
				# Print the partial line (halfline)
				# and the last half
				print $out_fh @$halfline_ref, substr($buf,0,$i);
			    }
			    # Buffer in memory for SQL and CSV-output
			    if($Global::membuffer) {
				push(@{$self->{'output'}{$fdno}},
				     @$halfline_ref, substr($buf,0,$i));
			    }
			    # Remove the printed part by keeping the unprinted
			    @$halfline_ref = (substr($buf,$i));
			}
		    } else {
			# No newline, so append to the halfline
			push @$halfline_ref, $buf;
		    }
		}
		$self->add_returnsize($outputlength);
		if($opt::latestline) { $self->print_latest_line($out_fh); }
	    }
	    if(defined $self->{'exitstatus'}) {
		if($Global::files or ($opt::results and not $Global::csvsep)) {
		    $self->add_returnsize(-s $self->fh($fdno,"name"));
		} else {
		    if($opt::latestline) {
			# Force re-computing color if --colorfailed
			if($opt::colorfailed) { delete $self->{'color'}; }
			if($self->{$out_fh,'latestline'} ne "") {
			    $self->print_latest_line($out_fh);
			}
			if(@{$self->{'halfline'}{$fdno}}) {
			    my $l = join('', @{$self->{'halfline'}{$fdno}});
			    if($l ne "") {
				$self->{$out_fh,'latestline'} = $l;
			    }
			} else {
			    $self->{$out_fh,'latestline'} = undef;
			}
			# Print latest line from jobs that are already done
			while($print_later{$minvisible}) {
			    $print_later{$minvisible}->print_latest_line($out_fh);
			    delete $print_later{$minvisible};
			    $minvisible++;
			}
			# Print latest line from jobs that are on screen now
			for(my $row = $minvisible;
			    $row < $minvisible -1 + ::terminal_rows();
			    $row++) {
			    $print_later{$row} and
				$print_later{$row}->print_latest_line($out_fh);
			}
		    } else {
			# If the job is dead: print the remaining partial line
			# read remaining (already done for $opt::latestline)
			my $halfline_ref = $self->{'halfline'}{$fdno};
			if(grep /./, @$halfline_ref) {
			    my $returnsize = 0;
			    for(@{$self->{'halfline'}{$fdno}}) {
				$returnsize += length $_;
			    }
			    $self->add_returnsize($returnsize);
			    if($opt::tag or defined $opt::tagstring) {
				# Prepend $tag the the remaining half line
				unshift @$halfline_ref, $self->tag();
			    }
			    # Print the partial line (halfline)
			    print $out_fh @{$self->{'halfline'}{$fdno}};
			    # Buffer in memory for SQL and CSV-output
			    if($Global::membuffer) {
				push(@{$self->{'output'}{$fdno}}, @$halfline_ref);
			    }
			    @$halfline_ref = ();
			}
		    }
		}
		if($self->fh($fdno,"rpid") and
		   CORE::kill 0, $self->fh($fdno,"rpid")) {
		    # decompress still running
		} else {
		    # decompress done: close fh
		    close $in_fh;
		    if($? and $opt::compress) {
			::error($opt::decompress_program." failed.");
			$self->set_exitstatus(255);
		    }
		}
	    }
	}
    }
}

sub free_ressources() {
    my $self = shift;
    if(not $opt::ungroup) {
	my $fh;
	for my $fdno (sort { $a <=> $b } keys %Global::fh) {
	    $fh = $self->fh($fdno,"w");
	    $fh and close $fh;
	    $fh = $self->fh($fdno,"r");
	    $fh and close $fh;
	}
    }
}

sub print_parset($) {
    # Wrap output with shell script code to set as variables
    my $self = shift;
    my ($fdno,$in_fh,$out_fh) = @_;
    my $outputlength = 0;

    ::debug("parset","print $Global::parset");
    if($Global::parset eq "assoc") {
	# Start: (done in parse_parset())
	#   eval "`echo 'declare -A myassoc; myassoc=(
	# Each: (done here)
	#   [$'a\tb']=$'a\tb\tc	 ddd'
	# End: (done in wait_and_exit())
	#   )'`"
	print '[',::Q($self->{'commandline'}->
		      replace_placeholders(["\257<\257>"],0,0)),']=';
    } elsif($Global::parset eq "array") {
	# Start: (done in parse_parset())
	#   eval "`echo 'myassoc=(
	# Each: (done here)
	#   $'a\tb\tc  ddd'
	# End: (done in wait_and_exit())
	#   )'`"
    } elsif($Global::parset eq "var") {
	# Start: (done in parse_parset())
	#   <empty>
	# Each: (done here)
	#   var=$'a\tb\tc  ddd'
	# End: (done in wait_and_exit())
	#   <empty>
	if(not @Global::parset_vars) {
	    ::error("Too few named destination variables");
	    ::wait_and_exit(255);
	}
	print shift @Global::parset_vars,"=";
    }
    local $/ = "\n";
    my $tag = $self->tag();
    my @out;
    while(<$in_fh>) {
	$outputlength += length $_;
	# Tag lines with \r, too
	$_ =~ s/(?<=[\r])(?=.|$)/$tag/gs;
	push @out, $tag,$_;
    }
    # Remove last newline
    # This often makes it easier to use the output in shell
    @out and ${out[$#out]} =~ s/\n$//s;
    print ::Q(join("",@out)),"\n";
    return $outputlength;
}

sub print_normal($) {
    my $self = shift;
    my ($fdno,$in_fh,$out_fh) = @_;
    my $buf;
    close $self->fh($fdno,"w");
    if($? and $opt::compress) {
	::error($opt::compress_program." failed.");
	$self->set_exitstatus(255);
    }
    if(not $self->virgin()) {
	seek $in_fh, 0, 0;
	# $in_fh is now ready for reading at position 0
	my $outputlength = 0;
	my @output;

	if($Global::parset and $fdno == 1) {
	    $outputlength += $self->print_parset($fdno,$in_fh,$out_fh);
	} elsif(defined $opt::tag or defined $opt::tagstring
		or $Global::color or $opt::colorfailed) {
	    if($Global::color or $opt::colorfailed) {
		my ($color,$reset_color) = $self->color();
		my $colortag = $color.$self->tag();
		# Read line by line
		local $/ = "\n";
		while(<$in_fh>) {
		    $outputlength += length $_;
		    # Tag lines with \r, too
		    chomp;
		    s{([\n\r])(?=.|$)}{$reset_color$1$colortag}gs;
		    print $out_fh $colortag,$_,$reset_color,"\n";
		}
	    } else {
		my $tag = $self->tag();
		my $pretag = 1;
		my $s;
		while(sysread($in_fh,$buf,32767)) {
		    $outputlength += length $buf;
		    $buf =~ s/(?<=[\r\n])(?=.)/$tag/gs;
		    print $out_fh ($pretag ? $tag : ""),$buf;
		    if($Global::membuffer) {
			push @{$self->{'output'}{$fdno}},
			    ($pretag ? $tag : ""),$buf;
		    }
		    # Should next print start with a tag?
		    $s = substr($buf, -1);
		    # This is faster than ($s eq "\n") || ($s eq "\r")
		    $pretag = ($s eq "\n") ? 1 : ($s eq "\r");
		}
	    }
	} else {
	    # Most efficient way of copying data from $in_fh to $out_fh
	    # Intel i7-3632QM: 25k-
	    while(sysread($in_fh,$buf,32767)) {
		print $out_fh $buf;
		$outputlength += length $buf;
		if($Global::membuffer) {
		    push @{$self->{'output'}{$fdno}}, $buf;
		}
	    }
	}
	if($fdno == 1) {
	    $self->add_returnsize($outputlength);
	}
	close $in_fh;
	if($? and $opt::compress) {
	    ::error($opt::decompress_program." failed.");
	    $self->set_exitstatus(255);
	}
    }
}

sub print_results($) {
    my $self = shift;
    my ($fdno,$in_fh,$out_fh) = @_;
    my $buf;
    close $self->fh($fdno,"w");
    if($? and $opt::compress) {
	::error($opt::compress_program." failed.");
	$self->set_exitstatus(255);
    }
    if(not $self->virgin()) {
	seek $in_fh, 0, 0;
	# $in_fh is now ready for reading at position 0
	my $outputlength = 0;
	my @output;

	if($Global::membuffer) {
	    # Read data into membuffer
	    if($opt::tag or $opt::tagstring) {
		# Read line by line
		local $/ = "\n";
		my $tag = $self->tag();
		while(<$in_fh>) {
		    $outputlength += length $_;
		    # Tag lines with \r, too
		    $_ =~ s/(?<=[\r])(?=.|$)/$tag/gs;
		    push @{$self->{'output'}{$fdno}}, $tag, $_;
		}
	    } else {
		# Most efficient way of copying data from $in_fh to $out_fh
		while(sysread($in_fh,$buf,60000)) {
		    $outputlength += length $buf;
		    push @{$self->{'output'}{$fdno}}, $buf;
		}
	    }
	} else {
	    # Not membuffer: No need to read the file
	    if($opt::compress) {
		$outputlength = -1;
	    } else {
		# Determine $outputlength = file length
		seek($in_fh, 0, 2) || ::die_bug("cannot seek result");
		$outputlength = tell($in_fh);
	    }
	}
	if($fdno == 1) { $self->add_returnsize($outputlength); }
	close $in_fh;
	if($? and $opt::compress) {
	    ::error($opt::decompress_program." failed.");
	    $self->set_exitstatus(255);
	}
    }
}

sub print_joblog($) {
    my $self = shift;
    my $cmd;
    if($Global::verbose <= 1) {
	$cmd = $self->replaced();
    } else {
	# Verbose level > 1: Print the rsync and stuff
	$cmd = $self->wrapped();
    }
    # Newlines make it hard to parse the joblog
    $cmd =~ s/\n/\0/g;
    print $Global::joblog
	join("\t", $self->seq(), $self->sshlogin()->string(),
	     $self->starttime(), sprintf("%10.3f",$self->runtime()),
	     $self->transfersize(), $self->returnsize(),
	     $self->exitstatus(), $self->exitsignal(), $cmd
	). "\n";
    flush $Global::joblog;
    $self->set_job_in_joblog();
}

sub tag($) {
    my $self = shift;
    if(not defined $self->{'tag'} or not $Global::cache_replacement_eval) {
	if(defined $opt::tag or defined $opt::tagstring) {
	    $self->{'tag'} =
		($self->{'commandline'}->
		 replace_placeholders([$opt::tagstring],0,0)).
		"\t";
	} else {
	    # No tag
	    $self->{'tag'} = "";
	}
    }
    return $self->{'tag'};
}

sub untabtag($) {
    # tag with \t replaced with spaces
    my $self = shift;
    my $tag = $self->tag();
    if(not defined $self->{'untab'}{$tag}) {
	$self->{'untab'}{$tag} = ::untabify($tag);
    }
    return $self->{'untab'}{$tag};
}

{
    my (@color,$eol,$reset_color,$init);

    sub init_color() {
	if(not $init) {
	    $init = 1;
	    # color combinations that are readable: black/white text
	    # on colored background, but not white on yellow
	    my @color_combinations =
		# Force each color code to have the same length in chars
		# This will make \t work as expected
		((map { [sprintf("%03d",$_),"000"] }
		  6..7,9..11,13..15,40..51,75..87,113..123,147..159,
		  171..182,185..231,249..254),
		 (map { [sprintf("%03d",$_),231] }
		  1..9,12..13,16..45,52..81,88..114,124..149,
		  160..178,180,182..184,196..214,232..250));
	    # reorder list so adjacent colors are dissimilar
	    # %23 and %7 were found experimentally
	    my @order =	reverse sort {
		    (($a%23) <=> ($b%23))
			or
			(($b%7) <=> ($a%7));
	    } 0..$#color_combinations;
	    @order = @order[54 .. $#color_combinations, 0 .. 53];
	    @color = map {
		# TODO Can this be done with `tput` codes?
		"\033[48;5;".$_->[0].";38;5;".$_->[1]."m"
	    } @color_combinations[ @order ];

	    # clr_eol el = clear to end of line
	    $eol = `sh -c "tput el </dev/tty" 2>/dev/null`;
	    chomp($eol);
	    if($eol eq "") { $eol = "\033[K"; }
	    # exit_attribute_mode sgr0 = turn off all attributes
	    $reset_color = `sh -c "tput sgr0 </dev/tty" 2>/dev/null`;
	    chomp($reset_color);
	    if($reset_color eq "") { $reset_color = "\033[m"; }
	}
    }

    sub color($) {
	my $self = shift;
	if(not defined $self->{'color'}) {
	    if($Global::color) {
		# Choose a value based on the seq
		$self->{'color'} = $color[$self->seq() % ($#color+1)].$eol;
		$self->{'reset_color'} = $reset_color;
	    } else {
		$self->{'color'} = "";
		$self->{'reset_color'} = "";
	    }
	    if($opt::colorfailed) {
		if($self->exitstatus()) {
		    # White on Red
		    # Can this be done more generally?
		    $self->{'color'} =
			"\033[48;5;"."196".";38;5;"."231"."m".$eol;
		    $self->{'reset_color'} = $reset_color;
		}
	    }
	}
	return ($self->{'color'},$self->{'reset_color'});
    }
}

sub hostgroups($) {
    my $self = shift;
    if(not defined $self->{'hostgroups'}) {
	$self->{'hostgroups'} =
	    $self->{'commandline'}->{'arg_list'}[0][0]->{'hostgroups'};
    }
    return @{$self->{'hostgroups'}};
}

sub exitstatus($) {
    my $self = shift;
    return $self->{'exitstatus'};
}

sub set_exitstatus($$) {
    my $self = shift;
    my $exitstatus = shift;
    if($exitstatus) {
	# Overwrite status if non-zero
	$self->{'exitstatus'} = $exitstatus;
    } else {
	# Set status but do not overwrite
	# Status may have been set by --timeout
	$self->{'exitstatus'} ||= $exitstatus;
    }
    $opt::sqlworker and
	$Global::sql->update("SET Exitval = ? WHERE Seq = ".$self->seq(),
			     $exitstatus);
}

sub reset_exitstatus($) {
    my $self = shift;
    undef $self->{'exitstatus'};
}

sub exitsignal($) {
    my $self = shift;
    return $self->{'exitsignal'};
}

sub set_exitsignal($$) {
    my $self = shift;
    my $exitsignal = shift;
    $self->{'exitsignal'} = $exitsignal;
    $opt::sqlworker and
	$Global::sql->update("SET _Signal = ? WHERE Seq = ".$self->seq(),
			     $exitsignal);
}

{
    my $total_jobs;

    sub should_we_halt {
	# Should we halt? Immediately? Gracefully?
	# Returns: N/A
	my $job = shift;
	my $limit;
	if($Global::semaphore) {
	    # Emulate Bash's +128 if there is a signal
	    $Global::halt_exitstatus =
		($job->exitstatus()
		 or
		 $job->exitsignal() ? $job->exitsignal() + 128 : 0);
	}
	if($job->exitstatus() or $job->exitsignal()) {
	    # Job failed
	    $Global::exitstatus++;
	    $Global::total_failed++;
	    if($Global::halt_fail) {
		::status("$Global::progname: This job failed:",
			 $job->replaced());
		$limit = $Global::total_failed;
	    }
	} elsif($Global::halt_success) {
	    ::status("$Global::progname: This job succeeded:",
		     $job->replaced());
	    $limit = $Global::total_completed - $Global::total_failed;
	}
	if($Global::halt_done) {
	    ::status("$Global::progname: This job finished:",
		     $job->replaced());
	    $limit = $Global::total_completed;
	}
	if(not defined $limit) {
	    return ""
	}
	#  --halt # => 1..100 (number of jobs failed, 101 means > 100)
	#  --halt % => 1..100 (pct of jobs failed)
	if($Global::halt_pct and not $Global::halt_count) {
	    $total_jobs ||= $Global::JobQueue->total_jobs();
	    # From the pct compute the number of jobs that must fail/succeed
	    $Global::halt_count = $total_jobs * $Global::halt_pct;
	}
	if($limit >= $Global::halt_count) {
	    # At least N jobs have failed/succeded/completed
	    # or at least N% have failed/succeded/completed
	    # So we should prepare for exit
	    if($Global::halt_fail or $Global::halt_done) {
		# Set exit status
		if(not defined $Global::halt_exitstatus) {
		    if($Global::halt_pct) {
			# --halt now,fail=X% or soon,fail=X%
			# --halt now,done=X% or soon,done=X%
			$Global::halt_exitstatus =
			    ::ceil($Global::total_failed / $total_jobs * 100);
		    } elsif($Global::halt_count) {
			# --halt now,fail=X or soon,fail=X
			# --halt now,done=X or soon,done=X
			$Global::halt_exitstatus =
			    ::min($Global::total_failed,101);
		    }
		    if($Global::halt_count and $Global::halt_count == 1) {
			# --halt now,fail=1 or soon,fail=1
			# --halt now,done=1 or soon,done=1
			# Emulate Bash's +128 if there is a signal
			$Global::halt_exitstatus =
			    ($job->exitstatus()
			     or
			     $job->exitsignal() ? $job->exitsignal() + 128 : 0);
		    }
		}
		::debug("halt","Pct: ",$Global::halt_pct,
			" count: ",$Global::halt_count,
			" status: ",$Global::halt_exitstatus,"\n");
	    } elsif($Global::halt_success) {
		$Global::halt_exitstatus = 0;
	    }
	    if($Global::halt_when eq "soon") {
		$Global::start_no_new_jobs ||= 1;
		if(scalar(keys %Global::running) > 0) {
		    # Only warn if there are more jobs running
		    ::status
			("$Global::progname: Starting no more jobs. ".
			 "Waiting for ". (keys %Global::running).
			 " jobs to finish.");
		}
	    }
	    return($Global::halt_when);
	}
	return "";
    }
}


package CommandLine;

sub new($) {
    my $class = shift;
    my $seq = shift;
    my $commandref = shift;
    $commandref || die;
    my $arg_queue = shift;
    my $context_replace = shift;
    my $max_number_of_args = shift; # for -N and normal (-n1)
    my $transfer_files = shift;
    my $return_files = shift;
    my $template_names = shift;
    my $template_contents = shift;
    my $replacecount_ref = shift;
    my $len_ref = shift;
    my %replacecount = %$replacecount_ref;
    my %len = %$len_ref;
    for (keys %$replacecount_ref) {
	# Total length of this replacement string {} replaced with all args
	$len{$_} = 0;
    }
    return bless {
	'command' => $commandref,
	'seq' => $seq,
	'len' => \%len,
	'arg_list' => [],
	'arg_list_flat' => [],
	'arg_list_flat_orig' => [undef],
	'arg_queue' => $arg_queue,
	'max_number_of_args' => $max_number_of_args,
	'replacecount' => \%replacecount,
	'context_replace' => $context_replace,
	'transfer_files' => $transfer_files,
	'return_files' => $return_files,
	'template_names' => $template_names,
	'template_contents' => $template_contents,
	'replaced' => undef,
    }, ref($class) || $class;
}

sub flush_cache() {
    my $self = shift;
    for my $arglist (@{$self->{'arg_list'}}) {
	for my $arg (@$arglist) {
	    $arg->flush_cache();
	}
    }
    $self->{'arg_queue'}->flush_cache();
    $self->{'replaced'} = undef;
}

sub seq($) {
    my $self = shift;
    return $self->{'seq'};
}

sub set_seq($$) {
    my $self = shift;
    $self->{'seq'} = shift;
}

sub slot($) {
    # Find the number of a free job slot and return it
    # Uses:
    #	@Global::slots - list with free jobslots
    # Returns:
    #	$jobslot = number of jobslot
    my $self = shift;
    if(not $self->{'slot'}) {
	if(not @Global::slots) {
	    # $max_slot_number will typically be $Global::max_jobs_running
	    push @Global::slots, ++$Global::max_slot_number;
	}
	$self->{'slot'} = shift @Global::slots;
    }
    return $self->{'slot'};
}

{
    my $already_spread;
    my $darwin_max_len;

    sub populate($) {
	# Add arguments from arg_queue until the number of arguments or
	# max line length is reached
	# Uses:
	#   $Global::usable_command_line_length
	#   $opt::cat
	#   $opt::fifo
	#   $Global::JobQueue
	#   $opt::m
	#   $opt::X
	#   $Global::max_jobs_running
	# Returns: N/A
	my $self = shift;
	my $next_arg;
	my $max_len = $Global::usable_command_line_length || die;
	if($^O eq "darwin") {
	    # Darwin's limit is affected by:
	    # * number of environment names (variables+functions)
	    # * size of environment
	    # * the length of arguments:
	    #	a one-char argument lowers the limit by 5
	    #	To be safe assume all arguments are one-char
	    # The max_len is cached between runs, but if the size of
	    # the environment is different we need to recompute the
	    # usable max length for this run of GNU Parallel
	    # See https://unix.stackexchange.com/a/604943/2972
	    if(not $darwin_max_len) {
		my $envc = (keys %ENV);
		my $envn = length join"",(keys %ENV);
		my $envv = length join"",(values %ENV);
		$darwin_max_len = -146+($max_len - $envn - $envv) - $envc*10;
		::debug("init",
			"length: $darwin_max_len ".
			"3+($max_len - $envn - $envv)/5 - $envc*2");
	    }
	    $max_len = $darwin_max_len;
	}
	if($opt::cat or $opt::fifo) {
	    # Get the empty arg added by --pipepart (if any)
	    $Global::JobQueue->{'commandlinequeue'}->{'arg_queue'}->get();
	    # $PARALLEL_TMP will point to a tempfile that will be used as {}
	    $Global::JobQueue->{'commandlinequeue'}->{'arg_queue'}->
		unget([Arg->new('"$PARALLEL_TMP"')]);
	}
	while (not $self->{'arg_queue'}->empty()) {
	    $next_arg = $self->{'arg_queue'}->get();
	    if(not defined $next_arg) {
		next;
	    }
	    $self->push($next_arg);
	    if($self->len() >= $max_len) {
		# Command length is now > max_length
		# If there are arguments: remove the last
		# If there are no arguments: Error
		# TODO stuff about -x opt_x
		if($self->number_of_args() > 1) {
		    # There is something to work on
		    $self->{'arg_queue'}->unget($self->pop());
		    last;
		} else {
		    my $args = join(" ", map { $_->orig() } @$next_arg);
		    ::error("Command line too long (".
			    $self->len(). " >= ".
			    $max_len.
			    ") at input ".
			    $self->{'arg_queue'}->arg_number().
			    ": ".
			    ((length $args > 50) ?
			     (substr($args,0,50))."..." :
			     $args));
		    $self->{'arg_queue'}->unget($self->pop());
		    ::wait_and_exit(255);
		}
	    }

	    if(defined $self->{'max_number_of_args'}) {
		if($self->number_of_args() >= $self->{'max_number_of_args'}) {
		    last;
		}
	    }
	}
	if(($opt::m or $opt::X) and not $already_spread
	   and $self->{'arg_queue'}->empty() and $Global::max_jobs_running) {
	    # -m or -X and EOF => Spread the arguments over all jobslots
	    # (unless they are already spread)
	    $already_spread ||= 1;
	    if($self->number_of_args() > 1) {
		$self->{'max_number_of_args'} =
		    ::ceil($self->number_of_args()/$Global::max_jobs_running);
		$Global::JobQueue->{'commandlinequeue'}->{'max_number_of_args'} =
		    $self->{'max_number_of_args'};
		$self->{'arg_queue'}->unget($self->pop_all());
		while($self->number_of_args() < $self->{'max_number_of_args'}) {
		    $self->push($self->{'arg_queue'}->get());
		}
	    }
	    $Global::JobQueue->flush_total_jobs();
	}

	if($opt::sqlmaster) {
	    # Insert the V1..Vn for this $seq in SQL table
	    # instead of generating one
	    $Global::sql->insert_records($self->seq(), $self->{'command'},
					 $self->{'arg_list_flat_orig'});
	}
    }
}

sub push($) {
    # Add one or more records as arguments
    # Returns: N/A
    my $self = shift;
    my $record = shift;
    push @{$self->{'arg_list_flat_orig'}}, map { $_->orig() } @$record;
    push @{$self->{'arg_list_flat'}}, @$record;
    push @{$self->{'arg_list'}}, $record;
    # Make @arg available for {= =}
    *Arg::arg = $self->{'arg_list_flat_orig'};

    my $quote_arg = ($Global::quote_replace and not $Global::quoting);
    my $col;
    for my $perlexpr (keys %{$self->{'replacecount'}}) {
	if($perlexpr =~ /^(-?\d+)(?:\D.*|)$/) {
	    # Positional replacement string
	    # Deal with negative positional replacement string
	    $col = ($1 < 0) ? $1 : $1-1;
	    if(defined($record->[$col])) {
		$self->{'len'}{$perlexpr} +=
		    length $record->[$col]->replace($perlexpr,$quote_arg,$self);
	    }
	} else {
	    for my $arg (@$record) {
		if(defined $arg) {
		    $self->{'len'}{$perlexpr} +=
			length $arg->replace($perlexpr,$quote_arg,$self);
		}
	    }
	}
    }
}

sub pop($) {
    # Remove last argument
    # Returns:
    #	the last record
    my $self = shift;
    my $record = pop @{$self->{'arg_list'}};
    # pop off arguments from @$record
    splice @{$self->{'arg_list_flat_orig'}}, -($#$record+1), $#$record+1;
    splice @{$self->{'arg_list_flat'}}, -($#$record+1), $#$record+1;
    my $quote_arg = ($Global::quote_replace and not $Global::quoting);
    for my $perlexpr (keys %{$self->{'replacecount'}}) {
	if($perlexpr =~ /^(\d+) /) {
	    # Positional
	    defined($record->[$1-1]) or next;
	    $self->{'len'}{$perlexpr} -=
		length $record->[$1-1]->replace($perlexpr,$quote_arg,$self);
	} else {
	    for my $arg (@$record) {
		if(defined $arg) {
		    $self->{'len'}{$perlexpr} -=
			length $arg->replace($perlexpr,$quote_arg,$self);
		}
	    }
	}
    }
    return $record;
}

sub pop_all($) {
    # Remove all arguments and zeros the length of replacement perlexpr
    # Returns:
    #	all records
    my $self = shift;
    my @popped = @{$self->{'arg_list'}};
    for my $perlexpr (keys %{$self->{'replacecount'}}) {
	$self->{'len'}{$perlexpr} = 0;
    }
    $self->{'arg_list'} = [];
    $self->{'arg_list_flat_orig'} = [undef];
    $self->{'arg_list_flat'} = [];
    return @popped;
}

sub number_of_args($) {
    # The number of records
    # Returns:
    #	number of records
    my $self = shift;
    # This is really the number of records
    return $#{$self->{'arg_list'}}+1;
}

sub number_of_recargs($) {
    # The number of args in records
    # Returns:
    #	number of args records
    my $self = shift;
    my $sum = 0;
    my $nrec = scalar @{$self->{'arg_list'}};
    if($nrec) {
	$sum = $nrec * (scalar @{$self->{'arg_list'}[0]});
    }
    return $sum;
}

sub args_as_string($) {
    # Returns:
    #  all unmodified arguments joined with ' ' (similar to {})
    my $self = shift;
    return (join " ", map { $_->orig() }
	    map { @$_ } @{$self->{'arg_list'}});
}

sub results_out($) {
    sub max_file_name_length {
	# Figure out the max length of a subdir
	# TODO and the max total length
	# Ext4 = 255,130816
	# Uses:
	#   $Global::max_file_length is set
	# Returns:
	#   $Global::max_file_length
	my $testdir = shift;

	my $upper = 100_000_000;
	# Dir length of 8 chars is supported everywhere
	my $len = 8;
	my $dir = "d"x$len;
	do {
	    rmdir($testdir."/".$dir);
	    $len *= 16;
	    $dir = "d"x$len;
	} while ($len < $upper and mkdir $testdir."/".$dir);
	# Then search for the actual max length between $len/16 and $len
	my $min = $len/16;
	my $max = $len;
	while($max-$min > 5) {
	    # If we are within 5 chars of the exact value:
	    # it is not worth the extra time to find the exact value
	    my $test = int(($min+$max)/2);
	    $dir = "d"x$test;
	    if(mkdir $testdir."/".$dir) {
		rmdir($testdir."/".$dir);
		$min = $test;
	    } else {
		$max = $test;
	    }
	}
	$Global::max_file_length = $min;
	return $min;
    }

    my $self = shift;
    my $out = $self->replace_placeholders([$opt::results],0,0);
    if($out eq $opt::results) {
	# $opt::results simple string: Append args_as_dirname
	my $args_as_dirname = $self->args_as_dirname(0);
	# Output in: prefix/name1/val1/name2/val2/stdout
	$out = $opt::results."/".$args_as_dirname;
	if(-d $out or eval{ File::Path::mkpath($out); }) {
	    # OK
	} else {
	    # mkpath failed: Argument too long or not quoted
	    # Set $Global::max_file_length, which will keep the individual
	    # dir names shorter than the max length
	    max_file_name_length($opt::results);
	    # Quote dirnames with +
	    $args_as_dirname = $self->args_as_dirname(1);
	    # prefix/name1/val1/name2/val2/
	    $out = $opt::results."/".$args_as_dirname;
	    File::Path::mkpath($out);
	}
	$out .="/";
    } else {
	if($out =~ m:/$:s) {
	    # / = dir
	    if(-d $out or eval{ File::Path::mkpath($out); }) {
		# OK
	    } else {
		::error("Cannot make dir '$out'.");
		::wait_and_exit(255);
	    }
	} else {
	    $out =~ m:(.*)/:s;
	    File::Path::mkpath($1);
	}
    }
    return $out;
}

{
    my %map;
    my %stringmap;
    my $sep;

    # test: '' . .. a. a.. + ++ 0..255 on fat12 ext4
    sub args_as_dirname($) {
	# Returns:
	#  all arguments joined with '/' (similar to {})
	#  Chars that are not safe on all file systems are quoted.
	sub init() {
	    # ext4: / \t \n \0 \\ \r
	    # fat: 0..31 " * / : < > ? \ | Maybe also: # [ ] ; = ,
	    # exfat: 128..255
	    # Other FS: , [ ] { } ( ) ! ; " ' * ? < > |
	    #
	    # Quote these as:
	    #   +  = ++
	    #   \0 = +0
	    #   \t = +t
	    #   \\ = +b (backslash)
	    #   \n = +n
	    #   \r = +r
	    #   / = +z (zlash)
	    #   ? = +y (whY?)
	    #   " = +d (double quote)
	    #   ' = +q (quote)
	    #   * = +a (asterisk)
	    #   < = +l (less than)
	    #   > = +g (greater than)
	    #   : = +k (kolon)
	    #   ! = +x (eXclamation)
	    #   | = +p (pipe)
	    #   # = +h (hash)
	    #   ; = +s (semicolon)
	    #   = = +e (equal)
	    #   , = +c (comma)
	    #   1..32 128..255 = +XX (hex value)
	    #   [ ] = +e +f
	    #   ( ) = +i +j
	    #   { } = +v +w
	    # Quote '' as +m (eMpty)
	    # Quote .  as +_
	    # Quote .. as +__
	    #   (Unused: ou)
	    %map = qw(
		+   ++
		\0  +0
		\t  +t
		\\  +b
		\n  +n
		\r  +r
		/   +z
		?   +y
		"   +d
		'   +q
		*   +a
		<   +l
		>   +g
		:   +k
		!   +x
		|   +p
		#   +h
		;   +s
		=   +e
		,   +c
		[   +e
		(   +i
		{   +v
		]   +f
		)   +j
		}   +w
		);
	    # 1..32 128..255 = +XX (hex value)
	    map { $map{sprintf "%c",$_} = sprintf "+%02x",$_ } 1..32, 128..255;
	    # Default value = itself
	    map { $map{sprintf "%c",$_} ||= sprintf "%c",$_ } 0..255;
	    # Quote '' as +m (eMpty)
	    $stringmap{""} = "+m";
	    # Quote .  as +_
	    $stringmap{"."} = "+_";
	    # Quote .. as +__
	    $stringmap{".."} = "+__";
	    # Set dir separator
	    eval 'use File::Spec; $sep = File::Spec->catfile("", "");';
	    $sep ||= '/';
	}
	# If $Global::max_file_length: Keep subdirs < $Global::max_file_length
	my $self = shift;
	my $quote = shift;
	my @res = ();
	if(not $sep) { init(); }

	for my $rec_ref (@{$self->{'arg_list'}}) {
	    # If headers are used, sort by them.
	    # Otherwise keep the order from the command line.
	    my @header_indexes_sorted = header_indexes_sorted($#$rec_ref+1);
	    for my $n (@header_indexes_sorted) {
		CORE::push(@res,
			   $Global::input_source_header{$n},
			   $quote ?
			   (
			    grep { $_ ne "\0noarg" } map {
				my $s = $_;
				# Quote + as ++
				$s =~ s/(.)/$map{$1}/gs;
				if($Global::max_file_length) {
				    # Keep each subdir shorter than the longest
				    # allowed file name
				    $s = substr($s,0,$Global::max_file_length);
				}
				$s; }
			    $rec_ref->[$n-1]->orig()
			   ) :
			   (
			    grep { $_ ne "\0noarg" } map {
				my $s = $_;
				# Quote / as +z and + as ++
				$s =~ s/($sep|\+)/$map{$1}/gos;
				if($Global::max_file_length) {
				    # Keep each subdir shorter than the longest
				    # allowed file name
				    $s = substr($s,0,$Global::max_file_length);
				}
				$s; }
			    $rec_ref->[$n-1]->orig()
			   )
		    );
	    }
	}
	return join $sep, map { $stringmap{$_} || $_ } @res;
    }
}

sub header_indexes_sorted($) {
    # Sort headers first by number then by name.
    # E.g.: 1a 1b 11a 11b
    # Returns:
    #  Indexes of %Global::input_source_header sorted
    my $max_col = shift;

    no warnings 'numeric';
    for my $col (1 .. $max_col) {
	# Make sure the header is defined. If it is not: use column number
	if(not defined $Global::input_source_header{$col}) {
	    $Global::input_source_header{$col} = $col;
	}
    }
    my @header_indexes_sorted = sort {
	# Sort headers numerically then asciibetically
	$Global::input_source_header{$a} <=> $Global::input_source_header{$b}
	or
	    $Global::input_source_header{$a} cmp $Global::input_source_header{$b}
    } 1 .. $max_col;
    return @header_indexes_sorted;
}

sub len($) {
    # Uses:
    #	@opt::shellquote
    # The length of the command line with args substituted
    my $self = shift;
    my $len = 0;
    # Add length of the original command with no args
    # Length of command w/ all replacement args removed
    $len += $self->{'len'}{'noncontext'} + @{$self->{'command'}} -1;
    ::debug("length", "noncontext + command: $len\n");
    # MacOS has an overhead of 8 bytes per argument
    my $darwin = ($^O eq "darwin") ? 8 : 0;
    my $recargs = $self->number_of_recargs();
    if($self->{'context_replace'}) {
	# Context is duplicated for each arg
	$len += $recargs * $self->{'len'}{'context'};
	for my $replstring (keys %{$self->{'replacecount'}}) {
	    # If the replacements string is more than once: mulitply its length
	    $len += $self->{'len'}{$replstring} *
		$self->{'replacecount'}{$replstring};
	    ::debug("length", $replstring, " ", $self->{'len'}{$replstring}, "*",
		    $self->{'replacecount'}{$replstring}, "\n");
	}
	# echo 11 22 33 44 55 66 77 88 99 1010
	# echo 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10
	# 5 +  ctxgrp*arg
	::debug("length", "Ctxgrp: ", $self->{'len'}{'contextgroups'},
		" Groups: ", $self->{'len'}{'noncontextgroups'}, "\n");
	# Add space between context groups
	$len += ($recargs-1) * ($self->{'len'}{'contextgroups'});
	if($darwin) {
	    $len += $recargs * $self->{'len'}{'contextgroups'} * $darwin;
	}
    } else {
	# Each replacement string may occur several times
	# Add the length for each time
	$len += 1*$self->{'len'}{'context'};
	::debug("length", "context+noncontext + command: $len\n");
	for my $replstring (keys %{$self->{'replacecount'}}) {
	    # (space between recargs + length of replacement)
	    # * number this replacement is used
	    $len += ($recargs -1 + $self->{'len'}{$replstring}) *
		$self->{'replacecount'}{$replstring};
	    if($darwin) {
		$len += ($recargs * $self->{'replacecount'}{$replstring}
			 * $darwin);
	    }
	}
    }
    if(defined $Global::parallel_env) {
	# If we are using --env, add the prefix for that, too.
	$len += length $Global::parallel_env;
    }
    if($Global::quoting) {
	# Pessimistic length if -q is set
	# Worse than worst case: ' => "'" + " => '"'
	# TODO can we count the number of expanding chars?
	#   and count them in arguments, too?
	$len *= 3;
    }
    if(@opt::shellquote) {
	# Pessimistic length if --shellquote is set
	# Worse than worst case: ' => "'"
	for(@opt::shellquote) {
	    $len *= 3;
	}
	$len *= 5;
    }
    if(@opt::sshlogin) {
	# Pessimistic length if remote
	# Worst case is BASE64 encoding 3 bytes -> 4 bytes
	$len = int($len*4/3);
    }
    return $len;
}

sub replaced($) {
    # Uses:
    #	$Global::quote_replace
    #	$Global::quoting
    # Returns:
    #	$replaced = command with place holders replaced and prepended
    my $self = shift;
    if(not defined $self->{'replaced'}) {
	# Don't quote arguments if the input is the full command line
	my $quote_arg = ($Global::quote_replace and not $Global::quoting);
	# or if ($opt::cat or $opt::pipe) as they use $PARALLEL_TMP
	$quote_arg = ($opt::cat || $opt::fifo) ? 0 : $quote_arg;
	$self->{'replaced'} = $self->
	    replace_placeholders($self->{'command'},$Global::quoting,
				 $quote_arg);
	my $len = length $self->{'replaced'};
	if ($len != $self->len()) {
	    ::debug("length", $len, " != ", $self->len(),
		    " ", $self->{'replaced'}, "\n");
	} else {
	    ::debug("length", $len, " == ", $self->len(),
		    " ", $self->{'replaced'}, "\n");
	}
    }
    return $self->{'replaced'};
}

sub replace_placeholders($$$$) {
    # Replace foo{}bar with fooargbar
    # Input:
    #	$targetref = command as shell words
    #	$quote = should everything be quoted?
    #	$quote_arg = should replaced arguments be quoted?
    # Uses:
    #	@Arg::arg = arguments as strings to be use in {= =}
    # Returns:
    #	@target with placeholders replaced
    my $self = shift;
    my $targetref = shift;
    my $quote = shift;
    my $quote_arg = shift;
    my %replace;

    # Token description:
    #	\0spc = unquoted space
    #	\0end = last token element
    #	\0ign = dummy token to be ignored
    #	\257<...\257> = replacement expression
    #	" " = quoted space, that splits -X group
    #	text = normal text - possibly part of -X group
    my $spacer = 0;
    my @tokens = grep { length $_ > 0 } map {
	if(/^\257<|^ $/) {
	    # \257<...\257> or space
	    $_
	} else {
	    # Split each space/tab into a token
	    split /(?=\s)|(?<=\s)/
	}
    }
    # Split \257< ... \257> into own token
    map { split /(?=\257<)|(?<=\257>)/ }
    # Insert "\0spc" between every element
    # This space should never be quoted
    map { $spacer++ ? ("\0spc",$_) : $_ }
    map { $_ eq "" ? "\0empty" : $_ }
    @$targetref;

    if(not @tokens) {
	# @tokens is empty: Return empty array
	return @tokens;
    }
    ::debug("replace", "Tokens ".join":",@tokens,"\n");
    # Make it possible to use $arg[2] in {= =}
    *Arg::arg = $self->{'arg_list_flat_orig'};
    # Flat list:
    # $self->{'arg_list'} = [ [Arg11, Arg12], [Arg21, Arg22], [Arg31, Arg32] ]
    # $self->{'arg_list_flat'} = [ Arg11, Arg12, Arg21, Arg22, Arg31, Arg32 ]
    if(not @{$self->{'arg_list_flat'}}) {
	@{$self->{'arg_list_flat'}} = Arg->new("");
    }
    my $argref = $self->{'arg_list_flat'};
    # Number of arguments - used for positional arguments
    my $n = $#$argref+1;

    # $self is actually a CommandLine-object,
    # but it looks nice to be able to say {= $job->slot() =}
    my $job = $self;
    # @replaced = tokens with \257< \257> replaced
    my @replaced;
    if($self->{'context_replace'}) {
	my @ctxgroup;
	for my $t (@tokens,"\0end") {
	    # \0end = last token was end of tokens.
	    if($t eq "\t" or $t eq " " or $t eq "\0end" or $t eq "\0spc") {
		# Context group complete: Replace in it
		if(grep { /^\257</ } @ctxgroup) {
		    # Context group contains a replacement string:
		    # Copy once per arg
		    my $space = "\0ign";
		    for my $arg (@$argref) {
			my $normal_replace;
			# Push output
			# Put unquoted space before each context group
			# except the first
			CORE::push @replaced, $space, map {
			    $a = $_;
			    if($a =~
				s{\257<(-?\d+)?(.*)\257>}
			    {
				if($1) {
				    # Positional replace
				    # Find the relevant arg and replace it
				    ($argref->[$1 > 0 ? $1-1 : $n+$1] ? # If defined: replace
				     $argref->[$1 > 0 ? $1-1 : $n+$1]->
				     replace($2,$quote_arg,$self)
				     : "");
				} else {
				    # Normal replace
				    $normal_replace ||= 1;
				    ($arg ? $arg->replace($2,$quote_arg,$self) : "");
				}
			    }sgxe) {
				# Token is \257<..\257>
			    } else {
				if($Global::escape_string_present) {
				    # Command line contains \257:
				    # Unescape it \257\256 => \257
				    $a =~ s/\257\256/\257/g;
				}
			    }
			    $a
			} @ctxgroup;
			$normal_replace or last;
			$space = "\0spc";
		    }
		} else {
		    # Context group has no a replacement string: Copy it once
		    CORE::push @replaced, map {
			$Global::escape_string_present and s/\257\256/\257/g; $_;
		    } @ctxgroup;
		}
		# New context group
		@ctxgroup=();
	    }
	    if($t eq "\0spc" or $t eq " ") {
		CORE::push @replaced,$t;
	    } else {
		CORE::push @ctxgroup,$t;
	    }
	}
    } else {
	# @group = @token
	# Replace in group
	# Push output
	# repquote = no if {} first on line, no if $quote, yes otherwise
	for my $t (@tokens) {
	    if($t =~ /^\257</) {
		my $space = "\0ign";
		for my $arg (@$argref) {
		    my $normal_replace;
		    $a = $t;
		    $a =~
			s{\257<(-?\d+)?(.*)\257>}
		    {
			if($1) {
			    # Positional replace
			    # Find the relevant arg and replace it
			    ($argref->[$1 > 0 ? $1-1 : $n+$1] ?
			     # If defined: replace
			     $argref->[$1 > 0 ? $1-1 : $n+$1]->
			     replace($2,$quote_arg,$self)
			     : "");
			} else {
			    # Normal replace
			    $normal_replace ||= 1;
			    ($arg ? $arg->replace($2,$quote_arg,$self) : "");
			}
		    }sgxe;
		    CORE::push @replaced, $space, $a;
		    $normal_replace or last;
		    $space = "\0spc";
		}
	    } else {
		# No replacement
		CORE::push @replaced, map {
		    $Global::escape_string_present and s/\257\256/\257/g; $_;
		} $t;
	    }
	}
    }
    *Arg::arg = [];
    ::debug("replace","Replaced: ".join":",@replaced,"\n");

    # Put tokens into groups that may be quoted.
    my @quotegroup;
    my @quoted;
    for (map { $_ eq "\0empty" ? "" : $_ }
	 grep { $_ ne "\0ign" and $_ ne "\0noarg" and $_ ne "'\0noarg'" }
	 @replaced, "\0end") {
	if($_ eq "\0spc" or $_ eq "\0end") {
	    # \0spc splits quotable groups
	    if($quote) {
		if(@quotegroup) {
		    CORE::push @quoted, ::Q(join"",@quotegroup);;
		}
	    } else {
		CORE::push @quoted, join"",@quotegroup;
	    }
	    @quotegroup = ();
	} else {
	    CORE::push @quotegroup, $_;
	}
    }
    ::debug("replace","Quoted: ".join":",@quoted,"\n");
    return wantarray ? @quoted : "@quoted";
}

sub skip($) {
    # Skip this job
    my $self = shift;
    $self->{'skip'} = 1;
}


package CommandLineQueue;

sub new($) {
    my $class = shift;
    my $commandref = shift;
    my $read_from = shift;
    my $context_replace = shift || 0;
    my $max_number_of_args = shift;
    my $transfer_files = shift;
    my $return_files = shift;
    my $template_names = shift;
    my $template_contents = shift;
    my @unget = ();
    my $posrpl;
    my ($replacecount_ref, $len_ref);
    my @command = @$commandref;
    my $seq = 1;
    # Replace replacement strings with {= perl expr =}
    # '{=' 'perlexpr' '=}'  => '{= perlexpr =}'
    @command = merge_rpl_parts(@command);

    # Protect matching inside {= perl expr =}
    # by replacing {= and =} with \257< and \257>
    # in options that can contain replacement strings:
    # @command, --transferfile, --return,
    # --tagstring, --workdir, --results
    for(@command, @$transfer_files, @$return_files,
	@$template_names, @$template_contents,
	$opt::tagstring, $opt::workdir, $opt::results, $opt::retries,
	@opt::filter) {
	# Skip if undefined
	defined($_) or next;
	# Escape \257 => \257\256
	$Global::escape_string_present += s/\257/\257\256/g;
	# Needs to match rightmost left parens (Perl defaults to leftmost)
	# to deal with: {={==} and {={==}=}
	# Replace {= -> \257<  and  =} -> \257>
	#
	# Complex way to do:
	#   s/{=(.*)=}/\257<$1\257>/g
	# which would not work
	s[\Q$Global::parensleft\E # Match {=
	  # Match . unless the next string is {= or =}
	  #   needed to force matching the shortest {= =}
	  ((?:(?! \Q$Global::parensleft\E|\Q$Global::parensright\E ).)*?)
	  \Q$Global::parensright\E ] # Match =}
	{\257<$1\257>}gxs;
	for my $rpl (sort { length $b <=> length $a } keys %Global::rpl) {
	    # Replace long --rpl's before short ones, as a short may be a
	    # substring of a long:
	    #	--rpl '% s/a/b/' --rpl '%% s/b/a/'
	    #
	    # Replace the shorthand string (--rpl)
	    # with the {= perl expr =}
	    #
	    # Avoid searching for shorthand strings inside existing {= perl expr =}
	    #
	    # Replace $$1 in {= perl expr =} with groupings in shorthand string
	    #
	    #	--rpl '{/(\.\S+)/(\.\S+)} s/$$1/$$2/g;'
	    #	  echo {/.tar/.gz} ::: UU.tar.gz
	    my ($prefix,$grp_regexp,$postfix) =
		$rpl =~ /^( [^(]*  )	# Prefix - e.g. {%%
			  ( \(.*\) )?	# Group capture regexp - e.g (.*)
			  ( [^)]*  )$	# Postfix - e.g }
			/xs;
	    $grp_regexp ||= '';
	    my $rplval = $Global::rpl{$rpl};
	    while(s{( (?: ^|\257> ) (?: [^\257]*|[\257][^<>] )*? )
		      # Don't replace after \257 unless \257>
		    \Q$prefix\E $grp_regexp \Q$postfix\E}
		  {
		      # The start remains the same
		      my $unchanged = $1;
		      # Dummy entry to start at 1.
		      my @grp = (1);
		      # $2 = first ()-group in $grp_regexp
		      # Put $2 in $grp[1], Put $3 in $grp[2]
		      # so first ()-group in $grp_regexp is $grp[1];
		      for(my $i = 2; defined $grp[$#grp]; $i++) {
			  push @grp, eval '$'.$i;
		      }
		      my $rv = $rplval;
		      # replace $$1 with $_pAr_gRp1, $$2 with $_pAr_gRp2
		      # in the code to be executed
		      $rv =~ s/\$\$ (\d+)/\$_pAr_gRp$1/gx;
		      # prepend with $_pAr_gRp1 = perlquote($1),
		      my $set_args = "";
		      for(my $i = 1;defined $grp[$i]; $i++) {
			  $set_args .= "\$_pAr_gRp$i = \"" .
			      ::perl_quote_scalar($grp[$i]) . "\";";
		      }
		      $unchanged . "\257<" . $set_args . $rv . "\257>"
		  }gxes) {
	    }
	    # Do the same for the positional replacement strings
	    $posrpl = $rpl;
	    if($posrpl =~ s/^\{//) {
		# Only do this if the shorthand start with {
		$prefix=~s/^\{//;
		# Don't replace after \257 unless \257>
		while(s{( (?: ^|\257> ) (?: [^\257]*|[\257][^<>] )*? )
		  \{(-?\d+) \s* \Q$prefix\E $grp_regexp \Q$postfix\E}
		      {
		      # The start remains the same
		      my $unchanged = $1;
		      my $position = $2;
		      # Dummy entry to start at 1.
		      my @grp = (1);
		      # $3 = first ()-group in $grp_regexp
		      # Put $3 in $grp[1], Put $4 in $grp[2]
		      # so first ()-group in $grp_regexp is $grp[1];
		      for(my $i = 3; defined $grp[$#grp]; $i++) {
			  push @grp, eval '$'.$i;
		      }
		      my $rv = $rplval;
		      # replace $$1 with $_pAr_gRp1, $$2 with $_pAr_gRp2
		      # in the code to be executed
		      $rv =~ s/\$\$ (\d+)/\$_pAr_gRp$1/gx;
		      # prepend with $_pAr_gRp1 = perlquote($1),
		      my $set_args = "";
		      for(my $i = 1;defined $grp[$i]; $i++) {
			  $set_args .= "\$_pAr_gRp$i = \"" .
			      ::perl_quote_scalar($grp[$i]) . "\";";
		      }
		      $unchanged . "\257<" . $position . $set_args . $rv . "\257>"
		  }gxes) {
		}
	    }
	}
    }
    # Add {} if no replacement strings in @command
    ($replacecount_ref, $len_ref, @command) =
	replacement_counts_and_lengths($transfer_files, $return_files,
				       $template_names, $template_contents,
				       @command);
    if("@command" =~ /^[^ \t\n=]*\257</) {
	# Replacement string is (part of) the command (and not just
	# argument or variable definition V1={})
	# E.g. parallel {}, parallel my_{= s/_//=}, parallel {2}
	# Do no quote (Otherwise it will fail if the input contains spaces)
	$Global::quote_replace = 0;
    }

    if($opt::sqlmaster and $Global::sql->append()) {
	$seq = $Global::sql->max_seq() + 1;
    }

    return bless {
	('unget' => \@unget,
	 'command' => \@command,
	 'replacecount' => $replacecount_ref,
	 'arg_queue' => RecordQueue->new($read_from,$opt::colsep),
	 'context_replace' => $context_replace,
	 'len' => $len_ref,
	 'max_number_of_args' => $max_number_of_args,
	 'size' => undef,
	 'transfer_files' => $transfer_files,
	 'return_files' => $return_files,
	 'template_names' => $template_names,
	 'template_contents' => $template_contents,
	 'seq' => $seq,
	 )
    }, ref($class) || $class;
}

sub merge_rpl_parts($) {
    # '{=' 'perlexpr' '=}'  => '{= perlexpr =}'
    # Input:
    #	@in = the @command as given by the user
    # Uses:
    #	$Global::parensleft
    #	$Global::parensright
    # Returns:
    #	@command with parts merged to keep {= and =} as one
    my @in = @_;
    my @out;
    my $l = quotemeta($Global::parensleft);
    my $r = quotemeta($Global::parensright);

    while(@in) {
	my $s = shift @in;
	$_ = $s;
	# Remove matching (right most) parens
	while(s/(.*)$l.*?$r/$1/os) {}
	if(/$l/o) {
	    # Missing right parens
	    while(@in) {
		$s .= " ".shift @in;
		$_ = $s;
		while(s/(.*)$l.*?$r/$1/os) {}
		if(not /$l/o) {
		    last;
		}
	    }
	}
	push @out, $s;
    }
    return @out;
}

sub replacement_counts_and_lengths($$@) {
    # Count the number of different replacement strings.
    # Find the lengths of context for context groups and non-context
    # groups.
    # If no {} found in @command: add it to @command
    #
    # Input:
    #	\@transfer_files = array of filenames to transfer
    #	\@return_files = array of filenames to return
    #	\@template_names = array of names to copy to
    #	\@template_contents = array of contents to write
    #	@command = command template
    # Output:
    #	\%replacecount, \%len, @command
    my $transfer_files = shift;
    my $return_files = shift;
    my $template_names = shift;
    my $template_contents = shift;
    my @command = @_;
    my (%replacecount,%len);
    my $sum = 0;
    while($sum == 0) {
	# Count how many times each replacement string is used
	my @cmd = @command;
	my $contextlen = 0;
	my $noncontextlen = 0;
	my $contextgroups = 0;
	for my $c (@cmd) {
	    while($c =~ s/ \257<( (?: [^\257]*|[\257][^<>] )*?)\257> /\000/xs) {
		# %replacecount = { "perlexpr" => number of times seen }
		# e.g { "s/a/b/" => 2 }
		$replacecount{$1}++;
		$sum++;
	    }
	    # Measure the length of the context around the {= perl expr =}
	    # Use that {=...=} has been replaced with \000 above
	    # So there is no need to deal with \257<
	    while($c =~ s/ (\S*\000\S*) //xs) {
		my $w = $1;
		$w =~ tr/\000//d; # Remove all \000's
		$contextlen += length($w);
		$contextgroups++;
	    }
	    # All {= perl expr =} have been removed: The rest is non-context
	    $noncontextlen += length $c;
	}
	for(@$transfer_files, @$return_files,
	    @$template_names, @$template_contents,
	    @opt::filter,
	    $opt::tagstring, $opt::workdir, $opt::results, $opt::retries) {
	    # Options that can contain replacement strings
	    defined($_) or next;
	    my $t = $_;
	    while($t =~ s/ \257<( (?: [^\257]*|[\257][^<>] )* )\257> //xs) {
		# %replacecount = { "perlexpr" => number of times seen }
		# e.g { "$_++" => 2 }
		# But for tagstring we just need to mark it as seen
		$replacecount{$1} ||= 1;
	    }
	}
	if($opt::bar) {
	    # If the command does not contain {} force it to be computed
	    # as it is being used by --bar
	    $replacecount{""} ||= 1;
	}

	$len{'context'} = 0+$contextlen;
	$len{'noncontext'} = $noncontextlen;
	$len{'contextgroups'} = $contextgroups;
	$len{'noncontextgroups'} = @cmd-$contextgroups;
	::debug("length", "@command Context: ", $len{'context'},
		" Non: ", $len{'noncontext'}, " Ctxgrp: ", $len{'contextgroups'},
		" NonCtxGrp: ", $len{'noncontextgroups'}, "\n");
	if($sum == 0) {
	    if(not @command) {
		# Default command = {}
		@command = ("\257<\257>");
	    } elsif(($opt::pipe or $opt::pipepart)
		    and not $opt::fifo and not $opt::cat) {
		# With --pipe / --pipe-part you can have no replacement
		last;
	    } else {
		# Append {} to the command if there are no {...}'s and no {=...=}
		push @command, ("\257<\257>");
	    }
	}
    }
    return(\%replacecount,\%len,@command);
}

sub get($) {
    my $self = shift;
    if(@{$self->{'unget'}}) {
	my $cmd_line = shift @{$self->{'unget'}};
	return ($cmd_line);
    } else {
	if($opt::sqlworker) {
	    # Get the sequence number from the SQL table
	    $self->set_seq($SQL::next_seq);
	    # Get the command from the SQL table
	    $self->{'command'} = $SQL::command_ref;
	    my @command;
	    # Recompute replace counts based on the read command
	    ($self->{'replacecount'},
	     $self->{'len'}, @command) =
		replacement_counts_and_lengths($self->{'transfer_files'},
					       $self->{'return_files'},
					       $self->{'template_name'},
					       $self->{'template_contents'},
					       @$SQL::command_ref);
	    if("@command" =~ /^[^ \t\n=]*\257</) {
		# Replacement string is (part of) the command (and not just
		# argument or variable definition V1={})
		# E.g. parallel {}, parallel my_{= s/_//=}, parallel {2}
		# Do no quote (Otherwise it will fail if the input contains spaces)
		$Global::quote_replace = 0;
	    }
	}

	my $cmd_line = CommandLine->new($self->seq(),
					$self->{'command'},
					$self->{'arg_queue'},
					$self->{'context_replace'},
					$self->{'max_number_of_args'},
					$self->{'transfer_files'},
					$self->{'return_files'},
					$self->{'template_names'},
					$self->{'template_contents'},
					$self->{'replacecount'},
					$self->{'len'},
	    );
	$cmd_line->populate();
	::debug("run","cmd_line->number_of_args ",
		$cmd_line->number_of_args(), "\n");
	if(not $Global::no_more_input and ($opt::pipe or $opt::pipepart)) {
	    if($cmd_line->replaced() eq "") {
		# Empty command - pipe requires a command
		::error("--pipe/--pipepart must have a command to pipe into ".
			"(e.g. 'cat').");
		::wait_and_exit(255);
	    }
	} elsif($cmd_line->number_of_args() == 0) {
	    # We did not get more args - maybe at EOF string?
	    return undef;
	}
	$self->set_seq($self->seq()+1);
	return $cmd_line;
    }
}

sub unget($) {
    my $self = shift;
    unshift @{$self->{'unget'}}, @_;
}

sub empty($) {
    my $self = shift;
    my $empty = (not @{$self->{'unget'}}) &&
	$self->{'arg_queue'}->empty();
    ::debug("run", "CommandLineQueue->empty $empty");
    return $empty;
}

sub seq($) {
    my $self = shift;
    return $self->{'seq'};
}

sub set_seq($$) {
    my $self = shift;
    $self->{'seq'} = shift;
}

sub quote_args($) {
    my $self = shift;
    # If there is not command emulate |bash
    return $self->{'command'};
}


package Limits::Command;

# Maximal command line length (for -m and -X)
sub max_length($) {
    # Find the max_length of a command line and cache it
    # Returns:
    #	number of chars on the longest command line allowed
    if(not $Limits::Command::line_max_len) {
	# Disk cache of max command line length
	my $len_cache = $Global::cache_dir . "/tmp/sshlogin/" . ::hostname() .
	    "/linelen";
	my $cached_limit;
	local $/ = undef;
	if(open(my $fh, "<", $len_cache)) {
	    $cached_limit = <$fh>;
	    $cached_limit || ::warning("Invalid content in $len_cache");
	    close $fh;
	}
	if(not $cached_limit) {
	    $cached_limit = real_max_length();
	    # If $HOME is write protected: Do not fail
	    my $dir = ::dirname($len_cache);
	    -d $dir or eval { File::Path::mkpath($dir); };
	    open(my $fh, ">", $len_cache.$$);
	    print $fh $cached_limit;
	    close $fh;
	    rename $len_cache.$$, $len_cache || ::die_bug("rename cache file");
	}
	$Limits::Command::line_max_len = tmux_length($cached_limit);
    }
    return int($Limits::Command::line_max_len);
}

sub real_max_length() {
    # Find the max_length of a command line
    # Returns:
    #	The maximal command line length with 1 byte arguments
    # return find_max(" c");
    return find_max("c");
}

sub find_max($) {
    my $string = shift;
    # This is slow on Cygwin, so give Cygwin users a warning
    if($^O eq "cygwin" or $^O eq "msys") {
	::warning("Finding the maximal command line length. ".
		  "This may take up to 1 minute.")
    }
    # Use an upper bound of 100 MB if the shell allows for infinite
    # long lengths
    my $upper = 100_000_000;
    my $lower;
    # 1000 is supported everywhere, so the search can start anywhere 1..999
    # 324 makes the search much faster on Cygwin, so let us use that
    my $len = 324;
    do {
	if($len > $upper) { return $len };
	$lower = $len;
	$len *= 4;
	::debug("init", "Maxlen: $lower<$len<$upper(".($upper-$lower)."): ");
    } while (is_acceptable_command_line_length($len,$string));
    # Then search for the actual max length between
    # last successful length ($len/16) and upper bound
    return binary_find_max(int($len/16),$len,$string);
}


# Prototype forwarding
sub binary_find_max($$$);
sub binary_find_max($$$) {
    # Given a lower and upper bound find the max (length or args) of a
    # command line
    # Returns:
    #   number of chars on the longest command line allowed
    my ($lower, $upper, $string) = (@_);
    if($lower == $upper
       or $lower == $upper-1
       or $lower/$upper > 0.99) {
        # $lower is +- 1 or within 1%: Don't search more
        return $lower;
    }
    # Unevenly split binary search which is faster for Microsoft Windows.
    # Guessing too high is cheap. Guessing too low is expensive.
    my $split = ($^O eq "cygwin" or $^O eq "msys") ? 0.93 : 0.5;
    my $middle = int (($upper-$lower)*$split + $lower);
    ::debug("init", "Maxlen: $lower<$middle<$upper(".($upper-$lower)."): ");
    if (is_acceptable_command_line_length($middle,$string)) {
        return binary_find_max($middle,$upper,$string);
    } else {
        return binary_find_max($lower,$middle,$string);
    }
}

{
    my $prg;

    sub is_acceptable_command_line_length($$) {
	# Test if a command line of this length can run
	# in the current environment
	# If the string is " x" it tests how many args are allowed
	# Returns:
	#   0 if the command line length is too long
	#   1 otherwise
	my $len = shift;
	my $string = shift;
	if($Global::parallel_env) {
	    $len += length $Global::parallel_env;
	}
	# Force using non-built-in command
	$prg ||= ::which("echo");
	my $l = length ::qqx("$prg ".${string}x(($len-1-length $prg)/length $string));
	if($l < $len/2) {
	    # The command returned OK, but did not output $len chars
	    # => this failed (Centos3 does this craziness)
	    return 0
	}
	::debug("init", "$len=$?\n");
	return not $?;
    }
}

sub tmux_length($) {
    # If $opt::tmux set, find the limit for tmux
    # tmux 1.8 has a 2kB limit
    # tmux 1.9 has a 16kB limit
    # tmux 2.0 has a 16kB limit
    # tmux 2.1 has a 16kB limit
    # tmux 2.2 has a 16kB limit
    # Input:
    #	$len = maximal command line length
    # Returns:
    #	$tmux_len = maximal length runable in tmux
    local $/ = "\n";
    my $len = shift;
    if($opt::tmux) {
	$ENV{'PARALLEL_TMUX'} ||= "tmux";
	if(not ::which($ENV{'PARALLEL_TMUX'})) {
	    ::error($ENV{'PARALLEL_TMUX'}." not found in \$PATH.");
	    ::wait_and_exit(255);
	}
	my @out;
	for my $l (1, 2020, 16320, 30000, $len) {
	    my $tmpfile = ::tmpname("tms");
	    my $qtmp = ::Q($tmpfile);
	    my $tmuxcmd = $ENV{'PARALLEL_TMUX'}.
		" -S $qtmp new-session -d -n echo $l".
		("t"x$l). " && echo $l; rm -f $qtmp";
	    push @out, ::qqx($tmuxcmd);
	    ::rm($tmpfile);
	}
	::debug("tmux","tmux-out ",@out);
	chomp @out;
	# The arguments is given 3 times on the command line
	# and the tmux wrapping is around 30 chars
	# (29 for tmux1.9, 33 for tmux1.8)
	my $tmux_len = ::max(@out);
	$len = ::min($len,int($tmux_len/4-33));
	::debug("tmux","tmux-length ",$len);
    }
    return $len;
}


package RecordQueue;

sub new($) {
    my $class = shift;
    my $fhs = shift;
    my $colsep = shift;
    my @unget = ();
    my $arg_sub_queue;
    if($opt::sqlworker) {
	# Open SQL table
	$arg_sub_queue = SQLRecordQueue->new();
    } elsif(defined $colsep) {
	# Open one file with colsep or CSV
	$arg_sub_queue = RecordColQueue->new($fhs);
    } else {
	# Open one or more files if multiple -a
	$arg_sub_queue = MultifileQueue->new($fhs);
    }
    return bless {
	'unget' => \@unget,
	'arg_number' => 0,
	'arg_sub_queue' => $arg_sub_queue,
    }, ref($class) || $class;
}

sub get($) {
    # Returns:
    #	reference to array of Arg-objects
    my $self = shift;
    if(@{$self->{'unget'}}) {
	$self->{'arg_number'}++;
	# Flush cached computed replacements in Arg-objects
	# To fix: parallel --bar echo {%} ::: a b c ::: d e f
	my $ret = shift @{$self->{'unget'}};
	if($ret) {
	    map { $_->flush_cache() } @$ret;
	}
	return $ret;
    }
    my $ret = $self->{'arg_sub_queue'}->get();
    if($ret) {
	if(grep { index($_->orig(),"\0") > 0 } @$ret) {
	    # Allow for \0 in position 0 because GNU  Parallel uses "\0noarg"
	    # to mean no-string
	    ::warning("A NUL character in the input was replaced with \\0.",
		      "NUL cannot be passed through in the argument list.",
		      "Did you mean to use the --null option?");
	    for(grep { index($_->orig(),"\0") > 0 } @$ret) {
		# Replace \0 with \\0
		my $a = $_->orig();
		$a =~ s/\0/\\0/g;
		$_->set_orig($a);
	    }
	}
	if(defined $Global::max_number_of_args
	   and $Global::max_number_of_args == 0) {
	    ::debug("run", "Read 1 but return 0 args\n");
	    # \0noarg => nothing (not the empty string)
	    map { $_->set_orig("\0noarg"); } @$ret;
	}
	# Flush cached computed replacements in Arg-objects
	# To fix: parallel --bar echo {%} ::: a b c ::: d e f
	map { $_->flush_cache() } @$ret;
    }
    return $ret;
}

sub unget($) {
    my $self = shift;
    ::debug("run", "RecordQueue-unget\n");
    $self->{'arg_number'} -= @_;
    unshift @{$self->{'unget'}}, @_;
}

sub empty($) {
    my $self = shift;
    my $empty = (not @{$self->{'unget'}}) &&
	$self->{'arg_sub_queue'}->empty();
    ::debug("run", "RecordQueue->empty $empty");
    return $empty;
}

sub flush_cache($) {
    my $self = shift;
    for my $record (@{$self->{'unget'}}) {
	for my $arg (@$record) {
	    $arg->flush_cache();
	}
    }
    $self->{'arg_sub_queue'}->flush_cache();
}

sub arg_number($) {
    my $self = shift;
    return $self->{'arg_number'};
}


package RecordColQueue;

sub new($) {
    my $class = shift;
    my $fhs = shift;
    my @unget = ();
    my $arg_sub_queue = MultifileQueue->new($fhs);
    return bless {
	'unget' => \@unget,
	'arg_sub_queue' => $arg_sub_queue,
    }, ref($class) || $class;
}

sub get($) {
    # Returns:
    #	reference to array of Arg-objects
    my $self = shift;
    if(@{$self->{'unget'}}) {
	return shift @{$self->{'unget'}};
    }
    if($self->{'arg_sub_queue'}->empty()) {
	return undef;
    }
    my $in_record = $self->{'arg_sub_queue'}->get();
    if(defined $in_record) {
	my @out_record = ();
	for my $arg (@$in_record) {
	    ::debug("run", "RecordColQueue::arg $arg\n");
	    my $line = $arg->orig();
	    ::debug("run", "line='$line'\n");
	    if($line ne "") {
		if($opt::csv) {
		    # Parse CSV and put it into a record
		    chomp $line;
		    if(not $Global::csv->parse($line)) {
			die "CSV has unexpected format: ^$line^";
		    }
		    for($Global::csv->fields()) {
			push @out_record, Arg->new($_);
		    }
		} else {
		    # Split --colsep into record
		    for my $s (split /$opt::colsep/o, $line, -1) {
			push @out_record, Arg->new($s);
		    }
		}
	    } else {
		push @out_record, Arg->new("");
	    }
	}
	return \@out_record;
    } else {
	return undef;
    }
}

sub unget($) {
    my $self = shift;
    ::debug("run", "RecordColQueue-unget '@_'\n");
    unshift @{$self->{'unget'}}, @_;
}

sub empty($) {
    my $self = shift;
    my $empty = (not @{$self->{'unget'}}) &&
	$self->{'arg_sub_queue'}->empty();
    ::debug("run", "RecordColQueue->empty $empty");
    return $empty;
}

sub flush_cache($) {
    my $self = shift;
    for my $arg (@{$self->{'unget'}}) {
	$arg->flush_cache();
    }
    $self->{'arg_sub_queue'}->flush_cache();
}


package SQLRecordQueue;

sub new($) {
    my $class = shift;
    my @unget = ();
    return bless {
	'unget' => \@unget,
    }, ref($class) || $class;
}

sub get($) {
    # Returns:
    #	reference to array of Arg-objects
    my $self = shift;
    if(@{$self->{'unget'}}) {
	return shift @{$self->{'unget'}};
    }
    return $Global::sql->get_record();
}

sub unget($) {
    my $self = shift;
    ::debug("run", "SQLRecordQueue-unget '@_'\n");
    unshift @{$self->{'unget'}}, @_;
}

sub empty($) {
    my $self = shift;
    if(@{$self->{'unget'}}) { return 0; }
    my $get = $self->get();
    if(defined $get) {
	$self->unget($get);
    }
    my $empty = not $get;
    ::debug("run", "SQLRecordQueue->empty $empty");
    return $empty;
}

sub flush_cache($) {
    my $self = shift;
    for my $record (@{$self->{'unget'}}) {
	for my $arg (@$record) {
	    $arg->flush_cache();
	}
    }
}


package MultifileQueue;

@Global::unget_argv=();

sub new($$) {
    my $class = shift;
    my $fhs = shift;
    for my $fh (@$fhs) {
	if(-t $fh and -t ($Global::status_fd || *STDERR)) {
	    ::warning(
		  "Input is read from the terminal. You are either an expert",
		  "(in which case: YOU ARE AWESOME!) or maybe you forgot",
		  "::: or :::: or -a or to pipe data into parallel. If so",
		  "consider going through the tutorial: man parallel_tutorial",
		  "Press CTRL-D to exit.");
	}
    }
    return bless {
	'unget' => \@Global::unget_argv,
	'fhs' => $fhs,
	'arg_matrix' => undef,
    }, ref($class) || $class;
}

sub get($) {
    my $self = shift;
    if($opt::link) {
	return $self->link_get();
    } else {
	return $self->nest_get();
    }
}

sub unget($) {
    my $self = shift;
    ::debug("run", "MultifileQueue-unget '@_'\n");
    unshift @{$self->{'unget'}}, @_;
}

sub empty($) {
    my $self = shift;
    my $empty = (not @Global::unget_argv) &&
	not @{$self->{'unget'}};
    for my $fh (@{$self->{'fhs'}}) {
	$empty &&= eof($fh);
    }
    ::debug("run", "MultifileQueue->empty $empty ");
    return $empty;
}

sub flush_cache($) {
    my $self = shift;
    for my $record (@{$self->{'unget'}}, @{$self->{'arg_matrix'}}) {
	for my $arg (@$record) {
	    $arg->flush_cache();
	}
    }
}

sub link_get($) {
    my $self = shift;
    if(@{$self->{'unget'}}) {
	return shift @{$self->{'unget'}};
    }
    my @record = ();
    my $prepend;
    my $empty = 1;
    for my $i (0..$#{$self->{'fhs'}}) {
	my $fh = $self->{'fhs'}[$i];
	my $arg = read_arg_from_fh($fh);
	if(defined $arg) {
	    # Record $arg for recycling at end of file
	    push @{$self->{'arg_matrix'}[$i]}, $arg;
	    push @record, $arg;
	    $empty = 0;
	} else {
	    ::debug("run", "EOA ");
	    # End of file: Recycle arguments
	    push @{$self->{'arg_matrix'}[$i]}, shift @{$self->{'arg_matrix'}[$i]};
	    # return last @{$args->{'args'}{$fh}};
	    push @record, @{$self->{'arg_matrix'}[$i]}[-1];
	}
    }
    if($empty) {
	return undef;
    } else {
	return \@record;
    }
}

sub nest_get($) {
    my $self = shift;
    if(@{$self->{'unget'}}) {
	return shift @{$self->{'unget'}};
    }
    my @record = ();
    my $prepend;
    my $empty = 1;
    my $no_of_inputsources = $#{$self->{'fhs'}} + 1;
    if(not $self->{'arg_matrix'}) {
	# Initialize @arg_matrix with one arg from each file
	# read one line from each file
	my @first_arg_set;
	my $all_empty = 1;
	for (my $fhno = 0; $fhno < $no_of_inputsources ; $fhno++) {
	    my $arg = read_arg_from_fh($self->{'fhs'}[$fhno]);
	    if(defined $arg) {
		$all_empty = 0;
	    }
	    $self->{'arg_matrix'}[$fhno][0] = $arg || Arg->new("");
	    push @first_arg_set, $self->{'arg_matrix'}[$fhno][0];
	}
	if($all_empty) {
	    # All filehandles were at eof or eof-string
	    return undef;
	}
	return [@first_arg_set];
    }

    # Treat the case with one input source special.  For multiple
    # input sources we need to remember all previously read values to
    # generate all combinations. But for one input source we can
    # forget the value after first use.
    if($no_of_inputsources == 1) {
	my $arg = read_arg_from_fh($self->{'fhs'}[0]);
	if(defined($arg)) {
	    return [$arg];
	}
	return undef;
    }
    for (my $fhno = $no_of_inputsources - 1; $fhno >= 0; $fhno--) {
	if(eof($self->{'fhs'}[$fhno])) {
	    next;
	} else {
	    # read one
	    my $arg = read_arg_from_fh($self->{'fhs'}[$fhno]);
	    defined($arg) || next; # If we just read an EOF string: Treat this as EOF
	    my $len = $#{$self->{'arg_matrix'}[$fhno]} + 1;
	    $self->{'arg_matrix'}[$fhno][$len] = $arg;
	    # make all new combinations
	    my @combarg = ();
	    for (my $fhn = 0; $fhn < $no_of_inputsources; $fhn++) {
		push(@combarg, [0, $#{$self->{'arg_matrix'}[$fhn]}],
		     # Is input source --link'ed to the next?
		     $opt::linkinputsource[$fhn+1]);
	    }
	    # Find only combinations with this new entry
	    $combarg[2*$fhno] = [$len,$len];
	    # map combinations
	    # [ 1, 3, 7 ], [ 2, 4, 1 ]
	    # =>
	    # [ m[0][1], m[1][3], m[2][7] ], [ m[0][2], m[1][4], m[2][1] ]
	    my @mapped;
	    for my $c (expand_combinations(@combarg)) {
		my @a;
		for my $n (0 .. $no_of_inputsources - 1 ) {
		    push @a,  $self->{'arg_matrix'}[$n][$$c[$n]];
		}
		push @mapped, \@a;
	    }
	    # append the mapped to the ungotten arguments
	    push @{$self->{'unget'}}, @mapped;
	    # get the first
	    if(@mapped) {
		return shift @{$self->{'unget'}};
	    }
	}
    }
    # all are eof or at EOF string; return from the unget queue
    return shift @{$self->{'unget'}};
}

{
    my $cr_count = 0;
    my $nl_count = 0;
    my $dos_crnl_determined;
    sub read_arg_from_fh($) {
	# Read one Arg from filehandle
	# Returns:
	#   Arg-object with one read line
	#   undef if end of file
	my $fh = shift;
	my $prepend;
	my $arg;
	my $half_record = 0;
	do {{
	    # This makes 10% faster
	    if(not defined ($arg = <$fh>)) {
		if(defined $prepend) {
		    return Arg->new($prepend);
		} else {
		    return undef;
		}
	    }
	    if(not $dos_crnl_determined and not defined $opt::d) {
		# Warn if input has CR-NL and -d is not set
		if($arg =~ /\r$/) {
		    $cr_count++;
		} else {
		    $nl_count++;
		}
		if($cr_count == 3 or $nl_count == 3) {
		    $dos_crnl_determined = 1;
		    if($nl_count == 0 and $cr_count == 3) {
			::warning('The first three values end in CR-NL. '.
				  'Consider using -d "\r\n"');
		    }
		}
	    }
	    if($opt::csv) {
		# We need to read a full CSV line.
		if(($arg =~ y/"/"/) % 2 ) {
		    # The number of " on the line is uneven:
		    # If we were in a half_record => we have a full record now
		    # If we were outside a half_record =>
		    #	 we are in a half record now
		    $half_record = not $half_record;
		}
		if($half_record) {
		    # CSV half-record with quoting:
		    #	col1,"col2 2""x3"" board newline  <-this one
		    #	cont",col3
		    $prepend .= $arg;
		    redo;
		} else {
		    # Now we have a full CSV record
		}
	    }
	    # Remove delimiter
	    chomp $arg;
	    if($Global::end_of_file_string and
	       $arg eq $Global::end_of_file_string) {
		# Ignore the rest of input file
		close $fh;
		::debug("run", "EOF-string ($arg) met\n");
		if(defined $prepend) {
		    return Arg->new($prepend);
		} else {
		    return undef;
		}
	    }
	    if(defined $prepend) {
		$arg = $prepend.$arg; # For line continuation
		undef $prepend;
	    }
	    if($Global::ignore_empty) {
		if($arg =~ /^\s*$/) {
		    redo; # Try the next line
		}
	    }
	    if($Global::max_lines) {
		if($arg =~ /\s$/) {
		    # Trailing space => continued on next line
		    $prepend = $arg;
		    redo;
		}
	    }
	    }} while (1 == 0); # Dummy loop {{}} for redo
	if(defined $arg) {
	    return Arg->new($arg);
	} else {
	    ::die_bug("multiread arg undefined");
	}
    }
}

# Prototype forwarding
sub expand_combinations(@);
sub expand_combinations(@) {
    # Input:
    #	([xmin,xmax], [ymin,ymax], ...)
    # Returns: ([x,y,...],[x,y,...])
    # where xmin <= x <= xmax and ymin <= y <= ymax
    my $minmax_ref = shift;
    my $link = shift; # This is linked to the next input source
    my $xmin = $$minmax_ref[0];
    my $xmax = $$minmax_ref[1];
    my @p;
    if(@_) {
	my @rest = expand_combinations(@_);
	if($link) {
	    # Linked to next col with --link/:::+/::::+
	    # TODO BUG does not wrap values if not same number of vals
	    push(@p, map { [$$_[0], @$_] }
		 grep { $xmin <= $$_[0] and $$_[0] <= $xmax } @rest);
	} else {
	    # If there are more columns: Compute those recursively
	    for(my $x = $xmin; $x <= $xmax; $x++) {
		push @p, map { [$x, @$_] } @rest;
	    }
	}
    } else {
	for(my $x = $xmin; $x <= $xmax; $x++) {
	    push @p, [$x];
	}
    }
    return @p;
}


package Arg;

sub new($) {
    my $class = shift;
    my $orig = shift;
    my @hostgroups;
    if($opt::hostgroups) {
	if($orig =~ s:@(.+)::) {
	    # We found hostgroups on the arg
	    @hostgroups = split(/\+|,/, $1);
	    if(not grep { defined $Global::hostgroups{$_} } @hostgroups) {
		# This hostgroup is not defined using -S
		# Add it
		::warning("Adding hostgroups: @hostgroups");
		# Add sshlogin
		for(grep { not defined $Global::hostgroups{$_} } @hostgroups) {
		    my $sshlogin = SSHLogin->new($_);
		    my $sshlogin_string = $sshlogin->string();
		    $Global::host{$sshlogin_string} = $sshlogin;
		    $Global::hostgroups{$sshlogin_string} = 1;
		}
	    }
	} else {
	    # No hostgroup on the arg => any hostgroup
	    @hostgroups = (keys %Global::hostgroups);
	}
    }
    return bless {
	'orig' => $orig,
	'hostgroups' => \@hostgroups,
    }, ref($class) || $class;
}

sub Q($) {
    # Q alias for ::shell_quote_scalar
    my $ret = ::Q($_[0]);
    no warnings 'redefine';
    *Q = \&::Q;
    return $ret;
}

sub pQ($) {
    # pQ alias for ::perl_quote_scalar
    my $ret = ::pQ($_[0]);
    no warnings 'redefine';
    *pQ = \&::pQ;
    return $ret;
}

sub hash($) {
    $Global::use{"DBI"} ||= eval "use B; 1;";
    B::hash(@_);
}

sub total_jobs() {
    return $Global::JobQueue->total_jobs();
}

{
    my %perleval;
    my $job;
    sub skip() {
	# shorthand for $job->skip();
	$job->skip();
    }
    sub slot() {
	# shorthand for $job->slot();
	$job->slot();
    }
    sub seq() {
	# shorthand for $job->seq();
	$job->seq();
    }
    sub uq() {
	# Do not quote this arg
	$Global::unquote_arg = 1;
    }
    sub yyyy_mm_dd_hh_mm_ss(@) {
	# ISO8601 2038-01-19T03:14:08
	::strftime("%Y-%m-%dT%H:%M:%S", localtime(shift || time()));
    }
    sub yyyy_mm_dd_hh_mm(@) {
	# ISO8601 2038-01-19T03:14
	::strftime("%Y-%m-%dT%H:%M", localtime(shift || time()));
    }
    sub yyyy_mm_dd(@) {
	# ISO8601 2038-01-19
	::strftime("%Y-%m-%d", localtime(shift || time()));
    }
    sub hh_mm_ss(@) {
	# ISO8601 03:14:08
	::strftime("%H:%M:%S", localtime(shift || time()));
    }
    sub hh_mm(@) {
	# ISO8601 03:14
	::strftime("%H:%M", localtime(shift || time()));
    }
    sub yyyymmddhhmmss(@) {
	# ISO8601 20380119 + ISO8601 031408
	::strftime("%Y%m%d%H%M%S", localtime(shift || time()));
    }
    sub yyyymmddhhmm(@) {
	# ISO8601 20380119 + ISO8601 0314
	::strftime("%Y%m%d%H%M", localtime(shift || time()));
    }
    sub yyyymmdd(@) {
	# ISO8601 20380119
	::strftime("%Y%m%d", localtime(shift || time()));
    }
    sub hhmmss(@) {
	# ISO8601 031408
	::strftime("%H%M%S", localtime(shift || time()));
    }
    sub hhmm(@) {
	# ISO8601 0314
	::strftime("%H%M", localtime(shift || time()));
    }

    sub replace($$$$) {
	# Calculates the corresponding value for a given perl expression
	# Returns:
	#   The calculated string (quoted if asked for)
	my $self = shift;
	my $perlexpr = shift; # E.g. $_=$_ or s/.gz//
	my $quote = shift; # should the string be quoted?
	# This is actually a CommandLine-object,
	# but it looks nice to be able to say {= $job->slot() =}
	$job = shift;
	# Positional replace treated as normal replace
	$perlexpr =~ s/^(-?\d+)? *//;
	if(not $Global::cache_replacement_eval
	   or
	   not $self->{'cache'}{$perlexpr}) {
	    # Only compute the value once
	    # Use $_ as the variable to change
	    local $_;
	    if($Global::trim eq "n") {
		$_ = $self->{'orig'};
	    } else {
		# Trim the input
		$_ = trim_of($self->{'orig'});
	    }
	    ::debug("replace", "eval ", $perlexpr, " ", $_, "\n");
	    if(not $perleval{$perlexpr}) {
		# Make an anonymous function of the $perlexpr
		# And more importantly: Compile it only once
		if($perleval{$perlexpr} =
		   eval('sub { no strict; no warnings; my $job = shift; '.
			$perlexpr.' }')) {
		    # All is good
		} else {
		    # The eval failed. Maybe $perlexpr is invalid perl?
		    ::error("Cannot use $perlexpr: $@");
		    ::wait_and_exit(255);
		}
	    }
	    # Execute the function
	    $perleval{$perlexpr}->($job);
	    $self->{'cache'}{$perlexpr} = $_;
	    if($Global::unquote_arg) {
		# uq() was called in perlexpr
		$self->{'cache'}{'unquote'}{$perlexpr} = 1;
		# Reset for next perlexpr
		$Global::unquote_arg = 0;
	    }
	}
	# Return the value quoted if needed
	if($self->{'cache'}{'unquote'}{$perlexpr}) {
	    return($self->{'cache'}{$perlexpr});
	} else {
	    return($quote ? Q($self->{'cache'}{$perlexpr})
		   : $self->{'cache'}{$perlexpr});
	}
    }
}

sub flush_cache($) {
    # Flush cache of computed values
    my $self = shift;
    $self->{'cache'} = undef;
}

sub orig($) {
    my $self = shift;
    return $self->{'orig'};
}

sub set_orig($$) {
    my $self = shift;
    $self->{'orig'} = shift;
}

sub trim_of($) {
    # Removes white space as specifed by --trim:
    # n = nothing
    # l = start
    # r = end
    # lr|rl = both
    # Returns:
    #	string with white space removed as needed
    my @strings = map { defined $_ ? $_ : "" } (@_);
    my $arg;
    if($Global::trim eq "n") {
	# skip
    } elsif($Global::trim eq "l") {
	for my $arg (@strings) { $arg =~ s/^\s+//; }
    } elsif($Global::trim eq "r") {
	for my $arg (@strings) { $arg =~ s/\s+$//; }
    } elsif($Global::trim eq "rl" or $Global::trim eq "lr") {
	for my $arg (@strings) { $arg =~ s/^\s+//; $arg =~ s/\s+$//; }
    } else {
	::error("--trim must be one of: r l rl lr.");
	::wait_and_exit(255);
    }
    return wantarray ? @strings : "@strings";
}


package TimeoutQueue;

sub new($) {
    my $class = shift;
    my $delta_time = shift;
    my ($pct);
    if($delta_time =~ /(\d+(\.\d+)?)%/) {
	# Timeout in percent
	$pct = $1/100;
	$delta_time = 1_000_000;
    }
    $delta_time = ::multiply_time_units($delta_time);

    return bless {
	'queue' => [],
	'delta_time' => $delta_time,
	'pct' => $pct,
	'remedian_idx' => 0,
	'remedian_arr' => [],
	'remedian' => undef,
    }, ref($class) || $class;
}

sub delta_time($) {
    my $self = shift;
    return $self->{'delta_time'};
}

sub set_delta_time($$) {
    my $self = shift;
    $self->{'delta_time'} = shift;
}

sub remedian($) {
    my $self = shift;
    return $self->{'remedian'};
}

sub set_remedian($$) {
    # Set median of the last 999^3 (=997002999) values using Remedian
    #
    # Rousseeuw, Peter J., and Gilbert W. Bassett Jr. "The remedian: A
    # robust averaging method for large data sets." Journal of the
    # American Statistical Association 85.409 (1990): 97-104.
    my $self = shift;
    my $val = shift;
    my $i = $self->{'remedian_idx'}++;
    my $rref = $self->{'remedian_arr'};
    $rref->[0][$i%999] = $val;
    $rref->[1][$i/999%999] = (sort @{$rref->[0]})[$#{$rref->[0]}/2];
    $rref->[2][$i/999/999%999] = (sort @{$rref->[1]})[$#{$rref->[1]}/2];
    $self->{'remedian'} = (sort @{$rref->[2]})[$#{$rref->[2]}/2];
}

sub update_median_runtime($) {
    # Update delta_time based on runtime of finished job if timeout is
    # a percentage
    my $self = shift;
    my $runtime = shift;
    if($self->{'pct'}) {
	$self->set_remedian($runtime);
	$self->{'delta_time'} = $self->{'pct'} * $self->remedian();
	::debug("run", "Timeout: $self->{'delta_time'}s ");
    }
}

sub process_timeouts($) {
    # Check if there was a timeout
    my $self = shift;
    # $self->{'queue'} is sorted by start time
    while (@{$self->{'queue'}}) {
	my $job = $self->{'queue'}[0];
	if($job->endtime()) {
	    # Job already finished. No need to timeout the job
	    # This could be because of --keep-order
	    shift @{$self->{'queue'}};
	} elsif($job->is_timedout($self->{'delta_time'})) {
	    # Need to shift off queue before kill
	    # because kill calls usleep that calls process_timeouts
	    shift @{$self->{'queue'}};
	    ::warning("This job was killed because it timed out:",
		      $job->replaced());
	    $job->kill();
	} else {
	    # Because they are sorted by start time the rest are later
	    last;
	}
    }
}

sub insert($) {
    my $self = shift;
    my $in = shift;
    push @{$self->{'queue'}}, $in;
}


package SQL;

sub new($) {
    my $class = shift;
    my $dburl = shift;
    $Global::use{"DBI"} ||= eval "use DBI; 1;";
    # +DBURL = append to this DBURL
    my $append = $dburl=~s/^\+//;
    my %options = parse_dburl(get_alias($dburl));
    my %driveralias = ("sqlite" => "SQLite",
		       "sqlite3" => "SQLite",
		       "pg" => "Pg",
		       "postgres" => "Pg",
		       "postgresql" => "Pg",
		       "csv" => "CSV",
		       "oracle" => "Oracle",
		       "ora" => "Oracle");
    my $driver = $driveralias{$options{'databasedriver'}} ||
	$options{'databasedriver'};
    my $database = $options{'database'};
    my $host = $options{'host'} ? ";host=".$options{'host'} : "";
    my $port = $options{'port'} ? ";port=".$options{'port'} : "";
    my $dsn = "DBI:$driver:dbname=$database$host$port";
    my $userid = $options{'user'};
    my $password = $options{'password'};;
    if(not grep /$driver/, DBI->available_drivers) {
	::error("$driver not supported. Are you missing a perl DBD::$driver module?");
	::wait_and_exit(255);
    }
    my $dbh;
    if($driver eq "CSV") {
	# CSV does not use normal dsn
	if(-d $database) {
	    $dbh = DBI->connect("dbi:CSV:", "", "", { f_dir => "$database", })
		or die $DBI::errstr;
	} else {
	    ::error("$database is not a directory.");
	    ::wait_and_exit(255);
	}
    } else {
	$dbh = DBI->connect($dsn, $userid, $password,
			   { RaiseError => 1, AutoInactiveDestroy => 1 })
	or die $DBI::errstr;
    }
    $dbh->{'PrintWarn'} = $Global::debug || 0;
    $dbh->{'PrintError'} = $Global::debug || 0;
    $dbh->{'RaiseError'} = 1;
    $dbh->{'ShowErrorStatement'} = 1;
    $dbh->{'HandleError'} = sub {};
    if(not defined $options{'table'}) {
	::error("The DBURL ($dburl) must contain a table.");
	::wait_and_exit(255);
    }

    return bless {
	'dbh' => $dbh,
	'driver' => $driver,
	'max_number_of_args' => undef,
	'table' => $options{'table'},
	'append' => $append,
    }, ref($class) || $class;
}

# Prototype forwarding
sub get_alias($);
sub get_alias($) {
    my $alias = shift;
    $alias =~ s/^(sql:)*//; # Accept aliases prepended with sql:
    if ($alias !~ /^:/) {
	return $alias;
    }

    # Find the alias
    my $path;
    if (-l $0) {
	($path) = readlink($0) =~ m|^(.*)/|;
    } else {
	($path) = $0 =~ m|^(.*)/|;
    }

    my @deprecated = ("$ENV{HOME}/.dburl.aliases",
		      "$path/dburl.aliases", "$path/dburl.aliases.dist");
    for (@deprecated) {
	if(-r $_) {
	    ::warning("$_ is deprecated. ".
		      "Use .sql/aliases instead (read man sql).");
	}
    }
    my @urlalias=();
    check_permissions("$ENV{HOME}/.sql/aliases");
    check_permissions("$ENV{HOME}/.dburl.aliases");
    my @search = ("$ENV{HOME}/.sql/aliases",
		  "$ENV{HOME}/.dburl.aliases", "/etc/sql/aliases",
		  "$path/dburl.aliases", "$path/dburl.aliases.dist");
    for my $alias_file (@search) {
	# local $/ needed if -0 set
	local $/ = "\n";
	if(-r $alias_file) {
	    open(my $in, "<", $alias_file) || die;
	    push @urlalias, <$in>;
	    close $in;
	}
    }
    my ($alias_part,$rest) = $alias=~/(:\w*)(.*)/;
    # If we saw this before: we have an alias loop
    if(grep {$_ eq $alias_part } @Private::seen_aliases) {
	::error("$alias_part is a cyclic alias.");
	exit -1;
    } else {
	push @Private::seen_aliases, $alias_part;
    }

    my $dburl;
    for (@urlalias) {
	/^$alias_part\s+(\S+.*)/ and do { $dburl = $1; last; }
    }

    if($dburl) {
	return get_alias($dburl.$rest);
    } else {
	::error("$alias is not defined in @search");
	exit(-1);
    }
}

sub check_permissions($) {
    my $file = shift;

    if(-e $file) {
	if(not -o $file) {
	    my $username = (getpwuid($<))[0];
	    ::warning("$file should be owned by $username: ".
		      "chown $username $file");
	}
	my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,
	    $atime,$mtime,$ctime,$blksize,$blocks) = stat($file);
	if($mode & 077) {
	    my $username = (getpwuid($<))[0];
	    ::warning("$file should be only be readable by $username: ".
		      "chmod 600 $file");
	}
    }
}

sub parse_dburl($) {
    my $url = shift;
    my %options = ();
    # sql:mysql://[[user][:password]@][host][:port]/[database[/table][?query]]

    if($url=~m!^(?:sql:)? # You can prefix with 'sql:'
	       ((?:oracle|ora|mysql|pg|postgres|postgresql)(?:s|ssl|)|
		 (?:sqlite|sqlite2|sqlite3|csv)):// # Databasedriver ($1)
	       (?:
		([^:@/][^:@]*|) # Username ($2)
		(?:
		 :([^@]*) # Password ($3)
		)?
	       @)?
	       ([^:/]*)? # Hostname ($4)
	       (?:
		:
		([^/]*)? # Port ($5)
	       )?
	       (?:
		/
		([^/?]*)? # Database ($6)
	       )?
	       (?:
		/
		([^?]*)? # Table ($7)
	       )?
	       (?:
		\?
		(.*)? # Query ($8)
	       )?
	      $!ix) {
	$options{databasedriver} = ::undef_if_empty(lc(uri_unescape($1)));
	$options{user} = ::undef_if_empty(uri_unescape($2));
	$options{password} = ::undef_if_empty(uri_unescape($3));
	$options{host} = ::undef_if_empty(uri_unescape($4));
	$options{port} = ::undef_if_empty(uri_unescape($5));
	$options{database} = ::undef_if_empty(uri_unescape($6));
	$options{table} = ::undef_if_empty(uri_unescape($7));
	$options{query} = ::undef_if_empty(uri_unescape($8));
	::debug("sql", "dburl $url\n");
	::debug("sql", "databasedriver ", $options{databasedriver},
		" user ", $options{user},
		" password ", $options{password}, " host ", $options{host},
		" port ", $options{port}, " database ", $options{database},
		" table ", $options{table}, " query ", $options{query}, "\n");
    } else {
	::error("$url is not a valid DBURL");
	exit 255;
    }
    return %options;
}

sub uri_unescape($) {
    # Copied from http://cpansearch.perl.org/src/GAAS/URI-1.55/URI/Escape.pm
    # to avoid depending on URI::Escape
    # This section is (C) Gisle Aas.
    # Note from RFC1630:  "Sequences which start with a percent sign
    # but are not followed by two hexadecimal characters are reserved
    # for future extension"
    my $str = shift;
    if (@_ && wantarray) {
	# not executed for the common case of a single argument
	my @str = ($str, @_);  # need to copy
	foreach (@str) {
	    s/%([0-9A-Fa-f]{2})/chr(hex($1))/eg;
	}
	return @str;
    }
    $str =~ s/%([0-9A-Fa-f]{2})/chr(hex($1))/eg if defined $str;
    $str;
}

sub run($) {
    my $self = shift;
    my $stmt = shift;
    if($self->{'driver'} eq "CSV") {
	$stmt=~ s/;$//;
	if($stmt eq "BEGIN" or
	   $stmt eq "COMMIT") {
	    return undef;
	}
    }
    my @retval;
    my $dbh = $self->{'dbh'};
    ::debug("sql","$opt::sqlmaster$opt::sqlworker run $stmt\n");
    # Execute with the rest of the args - if any
    my $rv;
    my $sth;
    my $lockretry = 0;
    while($lockretry < 10) {
	$sth = $dbh->prepare($stmt);
	if($sth
	   and
	   eval { $rv = $sth->execute(@_) }) {
	    last;
	} else {
	    if($@ =~ /no such table|Table .* doesn.t exist|relation ".*" does not exist/
	       or
	       $DBI::errstr =~ /no such table|Table .* doesn.t exist|relation ".*" does not exist/) {
		# This is fine:
		# It is just a worker that reported back too late -
		# another worker had finished the job first
		# and the table was then dropped
		$rv = $sth = 0;
		last;
	    }
	    if($DBI::errstr =~ /locked/) {
		::debug("sql", "Lock retry: $lockretry");
		$lockretry++;
		::usleep(rand()*300);
	    } elsif(not $sth) {
		# Try again
		$lockretry++;
	    } else {
		::error($DBI::errstr);
		::wait_and_exit(255);
	    }
	}
    }
    if($lockretry >= 10) {
	::die_bug("retry > 10: $DBI::errstr");
    }
    if($rv < 0 and $DBI::errstr){
	::error($DBI::errstr);
	::wait_and_exit(255);
    }
    return $sth;
}

sub get($) {
    my $self = shift;
    my $sth = $self->run(@_);
    my @retval;
    # If $sth = 0 it means the table was dropped by another process
    while($sth) {
	my @row = $sth->fetchrow_array();
	@row or last;
	push @retval, \@row;
    }
    return \@retval;
}

sub table($) {
    my $self = shift;
    return $self->{'table'};
}

sub append($) {
    my $self = shift;
    return $self->{'append'};
}

sub update($) {
    my $self = shift;
    my $stmt = shift;
    my $table = $self->table();
    $self->run("UPDATE $table $stmt",@_);
}

sub output($) {
    my $self = shift;
    my $commandline = shift;

    $self->update("SET Stdout = ?, Stderr = ? WHERE Seq = ".
		  $commandline->seq(),
		  join("",@{$commandline->{'output'}{1}}),
		  join("",@{$commandline->{'output'}{2}}));
}

sub max_number_of_args($) {
    # Maximal number of args for this table
    my $self = shift;
    if(not $self->{'max_number_of_args'}) {
	# Read the number of args from the SQL table
	my $table = $self->table();
	my $v = $self->get("SELECT * FROM $table LIMIT 1;");
	my @reserved_columns = qw(Seq Host Starttime JobRuntime Send
	    Receive Exitval _Signal Command Stdout Stderr);
	if(not $v) {
	    ::error("$table contains no records");
	}
	# Count the number of Vx columns
	$self->{'max_number_of_args'} = $#{$v->[0]} - $#reserved_columns;
    }
    return $self->{'max_number_of_args'};
}

sub set_max_number_of_args($$) {
    my $self = shift;
    $self->{'max_number_of_args'} = shift;
}

sub create_table($) {
    my $self = shift;
    if($self->append()) { return; }
    my $max_number_of_args = shift;
    $self->set_max_number_of_args($max_number_of_args);
    my $table = $self->table();
    $self->run(qq(DROP TABLE IF EXISTS $table;));
    # BIGINT and TEXT are not supported in these databases or are too small
    my %vartype = (
	"Oracle" => { "BIGINT" => "NUMBER(19,0)",
		      "TEXT" => "CLOB", },
	"mysql" => { "TEXT" => "BLOB", },
	"CSV" => { "BIGINT" => "INT",
		   "FLOAT" => "REAL", },
	);
    my $BIGINT = $vartype{$self->{'driver'}}{"BIGINT"} || "BIGINT";
    my $TEXT = $vartype{$self->{'driver'}}{"TEXT"} || "TEXT";
    my $FLOAT = $vartype{$self->{'driver'}}{"FLOAT"} || "FLOAT(44)";
    my $v_def = join "", map { "V$_ $TEXT," } (1..$self->max_number_of_args());
    $self->run(qq{CREATE TABLE $table
		(Seq $BIGINT,
		 Host $TEXT,
		 Starttime $FLOAT,
		 JobRuntime $FLOAT,
		 Send $BIGINT,
		 Receive $BIGINT,
		 Exitval $BIGINT,
		 _Signal $BIGINT,
		 Command $TEXT,}.
	       $v_def.
	       qq{Stdout $TEXT,
		 Stderr $TEXT);});
}

sub insert_records($) {
    my $self = shift;
    my $seq = shift;
    my $command_ref = shift;
    my $record_ref = shift;
    my $table = $self->table();
    # For SQL encode the command with \257 space as split points
    my $command = join("\257 ",@$command_ref);
    my @v_cols = map { ", V$_" } (1..$self->max_number_of_args());
    # Two extra value due to $seq, Exitval, Send
    my $v_vals = join ",", map { "?" } (1..$self->max_number_of_args()+4);
    $self->run("INSERT INTO $table (Seq,Command,Exitval,Send @v_cols) ".
	       "VALUES ($v_vals);", $seq, $command, -1000,
	       0, @$record_ref[1..$#$record_ref]);
}


sub get_record($) {
    my $self = shift;
    my @retval;
    my $table = $self->table();
    my @v_cols = map { ", V$_" } (1..$self->max_number_of_args());
    my $rand = "Reserved-".$$.rand();
    my $v;
    my $more_pending;

    do {
	if($self->{'driver'} eq "CSV") {
	    # Sub SELECT is not supported in CSV
	    # So to minimize the race condition below select a job at random
	    my $r = $self->get("SELECT Seq, Command @v_cols FROM $table ".
			       "WHERE Exitval = -1000 LIMIT 100;");
	    $v = [ sort { rand() > 0.5 } @$r ];
	} else {
	    # Avoid race condition where multiple workers get the same job
	    # by setting Stdout to a unique string
	    # (SELECT * FROM (...) AS dummy) is needed due to sillyness in MySQL
	    $self->update("SET Stdout = ?,Exitval = ? ".
			  "WHERE Seq = (".
			  "  SELECT * FROM (".
			  "    SELECT min(Seq) FROM $table WHERE Exitval = -1000".
			  "  ) AS dummy".
			  ") AND Exitval = -1000;", $rand, -1210);
	    # If a parallel worker overwrote the unique string this will get nothing
	    $v = $self->get("SELECT Seq, Command @v_cols FROM $table ".
			    "WHERE Stdout = ?;", $rand);
	}
	if($v->[0]) {
	    my $val_ref = $v->[0];
	    # Mark record as taken
	    my $seq = shift @$val_ref;
	    # Save the sequence number to use when running the job
	    $SQL::next_seq = $seq;
	    $self->update("SET Exitval = ? WHERE Seq = ".$seq, -1220);
	    # Command is encoded with '\257 space' as splitting char
	    my @command = split /\257 /, shift @$val_ref;
	    $SQL::command_ref = \@command;
	    for (@$val_ref) {
		push @retval, Arg->new($_);
	    }
	} else {
	    # If the record was updated by another job in parallel,
	    # then we may not be done, so see if there are more jobs pending
	    $more_pending =
		$self->get("SELECT Seq FROM $table WHERE Exitval = ?;", -1210);
	}
    } while (not $v->[0] and $more_pending->[0]);

    if(@retval) {
	return \@retval;
    } else {
	return undef;
    }
}

sub total_jobs($) {
    my $self = shift;
    my $table = $self->table();
    my $v = $self->get("SELECT count(*) FROM $table;");
    if($v->[0]) {
	return $v->[0]->[0];
    } else {
	::die_bug("SQL::total_jobs");
    }
}

sub max_seq($) {
    my $self = shift;
    my $table = $self->table();
    my $v = $self->get("SELECT max(Seq) FROM $table;");
    if($v->[0]) {
	return $v->[0]->[0];
    } else {
	::die_bug("SQL::max_seq");
    }
}

sub finished($) {
    # Check if there are any jobs left in the SQL table that do not
    # have a "real" exitval
    my $self = shift;
    if($opt::wait or $Global::start_sqlworker) {
	my $table = $self->table();
	my $rv = $self->get("select Seq,Exitval from $table ".
			    "where Exitval <= -1000 limit 1");
	return not $rv->[0];
    } else {
	return 1;
    }
}

package Semaphore;

# This package provides a counting semaphore
#
# If a process dies without releasing the semaphore the next process
# that needs that entry will clean up dead semaphores
#
# The semaphores are stored in $PARALLEL_HOME/semaphores/id-<name> Each
# file in $PARALLEL_HOME/semaphores/id-<name>/ is the process ID of the
# process holding the entry. If the process dies, the entry can be
# taken by another process.

sub new($) {
    my $class = shift;
    my $id = shift;
    my $count = shift;
    $id =~ s/([^-_a-z0-9])/unpack("H*",$1)/ige; # Convert non-word chars to hex
    $id = "id-".$id; # To distinguish it from a process id
    my $parallel_locks = $Global::cache_dir . "/semaphores";
    -d $parallel_locks or ::mkdir_or_die($parallel_locks);
    my $lockdir = "$parallel_locks/$id";
    my $lockfile = $lockdir.".lock";
    if(-d $parallel_locks and -w $parallel_locks
       and -r $parallel_locks and -x $parallel_locks) {
	# skip
    } else {
	::error("Semaphoredir must be writable: '$parallel_locks'");
	::wait_and_exit(255);
    }

    if($count < 1) { ::die_bug("semaphore-count: $count"); }
    return bless {
	'lockfile' => $lockfile,
	'lockfh' => Symbol::gensym(),
	'lockdir' => $lockdir,
	'id' => $id,
	'idfile' => $lockdir."/".$id,
	'pid' => $$,
	'pidfile' => $lockdir."/".$$.'@'.::hostname(),
	'count' => $count + 1 # nlinks returns a link for the 'id-' as well
    }, ref($class) || $class;
}

sub remove_dead_locks($) {
    my $self = shift;
    my $lockdir = $self->{'lockdir'};

    for my $d (glob "$lockdir/*") {
	$d =~ m:$lockdir/([0-9]+)\@([-\._a-z0-9]+)$:o or next;
	my ($pid, $host) = ($1, $2);
	if($host eq ::hostname()) {
	    if(kill 0, $pid) {
		::debug("sem", "Alive: $pid $d\n");
	    } else {
		::debug("sem", "Dead: $d\n");
		::rm($d);
	    }
	}
    }
}

sub acquire($) {
    my $self = shift;
    my $sleep = 1; # 1 ms
    my $start_time = time;
    while(1) {
	# Can we get a lock?
	$self->atomic_link_if_count_less_than() and last;
	$self->remove_dead_locks();
	# Retry slower and slower up to 1 second
	$sleep = ($sleep < 1000) ? ($sleep * 1.1) : ($sleep);
	# Random to avoid every sleeping job waking up at the same time
	::usleep(rand()*$sleep);
	if($opt::semaphoretimeout) {
	    if($opt::semaphoretimeout > 0
	       and
	       time - $start_time > $opt::semaphoretimeout) {
		# Timeout: Take the semaphore anyway
		::warning("Semaphore timed out. Stealing the semaphore.");
		if(not -e $self->{'idfile'}) {
		    open (my $fh, ">", $self->{'idfile'}) or
			::die_bug("timeout_write_idfile: $self->{'idfile'}");
		    close $fh;
		}
		link $self->{'idfile'}, $self->{'pidfile'};
		last;
	    }
	    if($opt::semaphoretimeout < 0
	       and
	       time - $start_time > -$opt::semaphoretimeout) {
		# Timeout: Exit
		::warning("Semaphore timed out. Exiting.");
		exit(1);
		last;
	    }
	}
    }
    ::debug("sem", "acquired $self->{'pid'}\n");
}

sub release($) {
    my $self = shift;
    ::rm($self->{'pidfile'});
    if($self->nlinks() == 1) {
	# This is the last link, so atomic cleanup
	$self->lock();
	if($self->nlinks() == 1) {
	    ::rm($self->{'idfile'});
	    rmdir $self->{'lockdir'};
	}
	$self->unlock();
    }
    ::debug("run", "released $self->{'pid'}\n");
}

sub pid_change($) {
    # This should do what release()+acquire() would do without having
    # to re-acquire the semaphore
    my $self = shift;

    my $old_pidfile =  $self->{'pidfile'};
    $self->{'pid'} = $$;
    $self->{'pidfile'} = $self->{'lockdir'}."/".$$.'@'.::hostname();
    my $retval = link $self->{'idfile'}, $self->{'pidfile'};
    ::debug("sem","link($self->{'idfile'},$self->{'pidfile'})=$retval\n");
    ::rm($old_pidfile);
}

sub atomic_link_if_count_less_than($) {
    # Link $file1 to $file2 if nlinks to $file1 < $count
    my $self = shift;
    my $retval = 0;
    $self->lock();
    my $nlinks = $self->nlinks();
    ::debug("sem","$nlinks<$self->{'count'} ");
    if($nlinks < $self->{'count'}) {
	-d $self->{'lockdir'} or ::mkdir_or_die($self->{'lockdir'});
	if(not -e $self->{'idfile'}) {
	    open (my $fh, ">", $self->{'idfile'}) or
		::die_bug("write_idfile: $self->{'idfile'}");
	    close $fh;
	}
	$retval = link $self->{'idfile'}, $self->{'pidfile'};
	::debug("sem","link($self->{'idfile'},$self->{'pidfile'})=$retval\n");
    }
    $self->unlock();
    ::debug("sem", "atomic $retval");
    return $retval;
}

sub nlinks($) {
    my $self = shift;
    if(-e $self->{'idfile'}) {
	return (stat(_))[3];
    } else {
	return 0;
    }
}

sub lock($) {
    my $self = shift;
    my $sleep = 100; # 100 ms
    my $total_sleep = 0;
    $Global::use{"Fcntl"} ||= eval "use Fcntl qw(:DEFAULT :flock); 1;";
    my $locked = 0;
    while(not $locked) {
	if(tell($self->{'lockfh'}) == -1) {
	    # File not open
	    open($self->{'lockfh'}, ">", $self->{'lockfile'})
		or ::debug("run", "Cannot open $self->{'lockfile'}");
	}
	if($self->{'lockfh'}) {
	    # File is open
	    chmod 0666, $self->{'lockfile'}; # assuming you want it a+rw
	    if(flock($self->{'lockfh'}, LOCK_EX()|LOCK_NB())) {
		# The file is locked: No need to retry
		$locked = 1;
		last;
	    } else {
		if ($! =~ m/Function not implemented/) {
		    ::warning("flock: $!",
			      "Will wait for a random while.");
		    ::usleep(rand(5000));
		    # File cannot be locked: No need to retry
		    $locked = 2;
		    last;
		}
	    }
	}
	# Locking failed in first round
	# Sleep and try again
	$sleep = ($sleep < 1000) ? ($sleep * 1.1) : ($sleep);
	# Random to avoid every sleeping job waking up at the same time
	::usleep(rand()*$sleep);
	$total_sleep += $sleep;
	if($opt::semaphoretimeout) {
	    if($opt::semaphoretimeout > 0
	       and
	       $total_sleep/1000 > $opt::semaphoretimeout) {
		# Timeout: Take the semaphore anyway
		::warning("Semaphore timed out. Taking the semaphore.");
		$locked = 3;
		last;
	    }
	    if($opt::semaphoretimeout < 0
	       and
	       $total_sleep/1000 > -$opt::semaphoretimeout) {
		# Timeout: Exit
		::warning("Semaphore timed out. Exiting.");
		$locked = 4;
		last;
	    }
	} else {
	    if($total_sleep/1000 > 30) {
		::warning("Semaphore stuck for 30 seconds. ".
			  "Consider using --semaphoretimeout.");
	    }
	}
    }
    ::debug("run", "locked $self->{'lockfile'}");
}

sub unlock($) {
    my $self = shift;
    ::rm($self->{'lockfile'});
    close $self->{'lockfh'};
    ::debug("run", "unlocked\n");
}

# Keep perl -w happy

$opt::x = $Semaphore::timeout = $Semaphore::wait =
$Job::file_descriptor_warning_printed = $Global::envdef = @Arg::arg =
$Global::max_slot_number = $opt::session;

package main;

sub main() {
    save_stdin_stdout_stderr();
    save_original_signal_handler();
    parse_options();
    ::debug("init", "Open file descriptors: ", join(" ",keys %Global::fh), "\n");
    my $number_of_args;
    if($Global::max_number_of_args) {
	$number_of_args = $Global::max_number_of_args;
    } elsif ($opt::X or $opt::m or $opt::xargs) {
	$number_of_args = undef;
    } else {
	$number_of_args = 1;
    }

    my @command = @ARGV;
    my @input_source_fh;
    if($opt::pipepart) {
	if($opt::tee) {
	    @input_source_fh = map { open_or_exit($_) } @opt::a;
	    # Remove the first: It will be the file piped.
	    shift @input_source_fh;
	    if(not @input_source_fh and not $opt::pipe) {
		@input_source_fh = (*STDIN);
	    }
	} else {
	    # -a is used for data - not for command line args
	    @input_source_fh = map { open_or_exit($_) } "/dev/null";
	}
    } else {
	@input_source_fh = map { open_or_exit($_) } @opt::a;
	if(not @input_source_fh and not $opt::pipe) {
	    @input_source_fh = (*STDIN);
	}
    }

    if($opt::skip_first_line) {
	# Skip the first line for the first file handle
	my $fh = $input_source_fh[0];
	<$fh>;
    }

    set_input_source_header(\@command,\@input_source_fh);
    if($opt::filter_hosts and (@opt::sshlogin or @opt::sshloginfile)) {
	# Parallel check all hosts are up. Remove hosts that are down
	filter_hosts();
    }
    if($opt::sqlmaster and $opt::sqlworker) {
	# Start a real --sqlworker in the background later
	$Global::start_sqlworker = 1;
	$opt::sqlworker = undef;
    }

    if($opt::nonall or $opt::onall) {
	onall(\@input_source_fh,@command);
	wait_and_exit(min(undef_as_zero($Global::exitstatus),254));
    }

    $Global::JobQueue = JobQueue->new(
	\@command, \@input_source_fh, $Global::ContextReplace,
	$number_of_args, \@Global::transfer_files, \@Global::ret_files,
	\@Global::template_names, \@Global::template_contents
	);

    if($opt::sqlmaster) {
	# Create SQL table to hold joblog + output
	# Figure out how many arguments are in a job
	# (It is affected by --colsep, -N, $number_source_fh)
	my $record_queue = $Global::JobQueue->{'commandlinequeue'}{'arg_queue'};
	my $record = $record_queue->get();
	my $no_of_values = $number_of_args * (1+$#{$record});
	$record_queue->unget($record);
	$Global::sql->create_table($no_of_values);
	if($opt::sqlworker) {
	    # Start a real --sqlworker in the background later
	    $Global::start_sqlworker = 1;
	    $opt::sqlworker = undef;
	}
    }

    if($opt::pipepart) {
	pipepart_setup();
    } elsif($opt::pipe) {
	if($opt::tee) {
	    pipe_tee_setup();
	} elsif($opt::shard or $opt::bin) {
	    pipe_shard_setup();
	} elsif($opt::groupby) {
	    pipe_group_by_setup();
	}
    }

    if($opt::eta or $opt::bar or $opt::shuf or $Global::halt_pct) {
	# Count the number of jobs or shuffle all jobs
	# before starting any.
	# Must be done after ungetting any --pipepart jobs.
	$Global::JobQueue->total_jobs();
    }
    # Compute $Global::max_jobs_running
    # Must be done after ungetting any --pipepart jobs.
    max_jobs_running();
    init_run_jobs();
    my $sem;
    if($Global::semaphore) {
	$sem = acquire_semaphore();
    }
    $SIG{TERM} = $Global::original_sig{TERM};
    $SIG{HUP} = \&start_no_new_jobs;

    if($opt::tee or $opt::shard or $opt::bin) {
	# All jobs must be running in parallel for --tee/--shard/--bin
	while(start_more_jobs()) {}
	$Global::start_no_new_jobs = 1;
	if(not $Global::JobQueue->empty()) {
	    if($opt::tee) {
		::error("--tee requires --jobs to be higher. Try --jobs 0.");
	    } elsif($opt::bin) {
		::error("--bin requires --jobs to be higher than the number of",
			"arguments. Increase --jobs.");
	    } elsif($opt::shard) {
		::error("--shard requires --jobs to be higher than the number of",
			"arguments. Increase --jobs.");
	    } else {
		::die_bug("--bin/--shard/--tee should not get here");
	    }
	    ::wait_and_exit(255);
	}
    } elsif($opt::pipe and not $opt::pipepart and not $opt::semaphore) {
	# Fill all jobslots
	while(start_more_jobs()) {}
	spreadstdin();
    } else {
	# Reap the finished jobs and start more
	while(reapers() + start_more_jobs()) {}
    }
    ::debug("init", "Start draining\n");
    drain_job_queue(@command);
    ::debug("init", "Done draining\n");
    reapers();
    ::debug("init", "Done reaping\n");
    if($Global::semaphore) { $sem->release(); }
    cleanup();
    ::debug("init", "Halt\n");
    halt();
}

main();
cut-here-V93TWypzvAaP5RvzZfUv

    # Copy the source code from the file to the fifo
    # and remove the file and fifo ASAP
    # 'sh -c' is needed to avoid
    #	[1]+  Done   cat
    sh -c "(rm $_file_with_GNU_Parallel_source; cat >$_fifo_with_GNU_Parallel_source; rm $_fifo_with_GNU_Parallel_source) < $_file_with_GNU_Parallel_source &"

    # Read the source from the fifo
    perl $_fifo_with_GNU_Parallel_source "$@"
}
#!/usr/bin/bash

# This file must be sourced in bash:
#
#   source env_parallel.bash
#
# after which 'env_parallel' works
#
#
# Copyright (C) 2016-2023 Ole Tange, http://ole.tange.dk and Free
# Software Foundation, Inc.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, see <http://www.gnu.org/licenses/>
# or write to the Free Software Foundation, Inc., 51 Franklin St,
# Fifth Floor, Boston, MA 02110-1301 USA
#
# SPDX-FileCopyrightText: 2021-2023 Ole Tange, http://ole.tange.dk and Free Software and Foundation, Inc.
# SPDX-License-Identifier: GPL-3.0-or-later
# shellcheck disable=SC2006

env_parallel() {
    # env_parallel.bash

    _names_of_ALIASES() {
	# No aliases will return false. This error should be ignored.
	compgen -a || true
    }
    _bodies_of_ALIASES() {
	local _i
	for _i in "$@"; do
	    # shellcheck disable=SC2046
	    if [ $(alias "$_i" | wc -l) == 1 ] ; then
		true Alias is a single line. Good.
	    else
		_warning_PAR "Alias '$_i' contains newline."
		_warning_PAR "Make sure the command has at least one newline after '$_i'."
		_warning_PAR "See BUGS in 'man env_parallel'."
	    fi
	done
	alias "$@"
    }
    _names_of_FUNCTIONS() {
	compgen -A function
    }
    _bodies_of_FUNCTIONS() {
	typeset -f "$@"
    }
    _names_of_VARIABLES() {
	compgen -A variable
    }
    _bodies_of_VARIABLES() {
	typeset -p "$@"
    }
    _ignore_HARDCODED() {
	# Copying $RANDOM will cause it not to be random
	# The rest cannot be detected as read-only
	echo '(RANDOM|_|TIMEOUT|GROUPS|FUNCNAME|DIRSTACK|PIPESTATUS|USERNAME|BASHPID|BASH_[A-Z_]+)'
    }
    _ignore_READONLY() {
	# shellcheck disable=SC1078,SC1079,SC2026
	readonly | perl -e '@r = map {
                chomp;
                # sh on UnixWare: readonly TIMEOUT
	        # ash: readonly var='val'
	        # ksh: var='val'
		# mksh: PIPESTATUS[0]
                s/^(readonly )?([^=\[ ]*?)(\[\d+\])?(=.*|)$/$2/ or
	        # bash: declare -ar BASH_VERSINFO=([0]="4" [1]="4")
	        # zsh: typeset -r var='val'
                  s/^\S+\s+\S+\s+(\S[^=]*)(=.*|$)/$1/;
                $_ } <>;
            $vars = join "|",map { quotemeta $_ } @r;
            print $vars ? "($vars)" : "(,,nO,,VaRs,,)";
            '
    }
    _remove_bad_NAMES() {
	# Do not transfer vars and funcs from env_parallel
	# shellcheck disable=SC2006
	_ignore_RO="`_ignore_READONLY`"
	# shellcheck disable=SC2006
	_ignore_HARD="`_ignore_HARDCODED`"
	# To avoid depending on grep dialect, use Perl version of:
	# grep -Ev '^(...)$' |
	perl -ne '/^(
		     PARALLEL_ENV|
		     PARALLEL_TMP|
		     _alias_NAMES|
		     _bodies_of_ALIASES|
		     _bodies_of_FUNCTIONS|
		     _bodies_of_VARIABLES|
		     _error_PAR|
		     _function_NAMES|
		     _get_ignored_VARS|
		     _grep_REGEXP|
		     _ignore_HARD|
		     _ignore_HARDCODED|
		     _ignore_READONLY|
		     _ignore_RO|
		     _ignore_UNDERSCORE|
		     _list_alias_BODIES|
		     _list_function_BODIES|
		     _list_variable_VALUES|
		     _make_grep_REGEXP|
		     _names_of_ALIASES|
		     _names_of_FUNCTIONS|
		     _names_of_VARIABLES|
		     _names_of_maybe_FUNCTIONS|
		     _parallel_exit_CODE|
		     _prefix_PARALLEL_ENV|
		     _prefix_PARALLEL_ENV|
		     _remove_bad_NAMES|
		     _remove_readonly|
		     _variable_NAMES|
		     _warning_PAR|
		     _which_PAR)$/x and next;
	    # Filter names matching --env
	    /^'"$_grep_REGEXP"'$/ or next;
            /^'"$_ignore_UNDERSCORE"'$/ and next;
	    # Remove readonly variables
            /^'"$_ignore_RO"'$/ and next;
            /^'"$_ignore_HARD"'$/ and next;
            print;'
    }
    _prefix_PARALLEL_ENV() {
        shopt 2>/dev/null |
        perl -pe 's:\s+off:;: and s/^/shopt -u /;
                  s:\s+on:;: and s/^/shopt -s /;
                  s:;$:&>/dev/null;:';
        echo 'shopt -s expand_aliases &>/dev/null';
    }

    _get_ignored_VARS() {
        perl -e '
            for(@ARGV){
                $next_is_env and push @envvar, split/,/, $_;
                $next_is_env=/^--env$/;
            }
            if(grep { /^_$/ } @envvar) {
                if(not open(IN, "<", "$ENV{HOME}/.parallel/ignored_vars")) {
             	    print STDERR "parallel: Error: ",
            	    "Run \"parallel --record-env\" in a clean environment first.\n";
                } else {
            	    chomp(@ignored_vars = <IN>);
                }
            }
            if($ENV{PARALLEL_IGNORED_NAMES}) {
                push @ignored_vars, split/\s+/, $ENV{PARALLEL_IGNORED_NAMES};
                chomp @ignored_vars;
            }
            $vars = join "|",map { quotemeta $_ } @ignored_vars;
	    print $vars ? "($vars)" : "(,,nO,,VaRs,,)";
            ' -- "$@"
    }

    # Get the --env variables if set
    # --env _ should be ignored
    # and convert  a b c  to (a|b|c)
    # If --env not set: Match everything (.*)
    _make_grep_REGEXP() {
        perl -e '
            for(@ARGV){
                /^_$/ and $next_is_env = 0;
                $next_is_env and push @envvar, split/,/, $_;
                $next_is_env = /^--env$/;
            }
            $vars = join "|",map { quotemeta $_ } @envvar;
            print $vars ? "($vars)" : "(.*)";
            ' -- "$@"
    }
    _which_PAR() {
	# type returns:
	#   ll is an alias for ls -l (in ash)
	#   bash is a tracked alias for /bin/bash
	#   true is a shell builtin (in bash)
	#   myfunc is a function (in bash)
	#   myfunc is a shell function (in zsh)
	#   which is /usr/bin/which (in sh, bash)
	#   which is hashed (/usr/bin/which)
	#   gi is aliased to `grep -i' (in bash)
	#   aliased to `alias | /usr/bin/which --tty-only --read-alias --show-dot --show-tilde'
	# Return 0 if found, 1 otherwise
	LANG=C type "$@" |
	    perl -pe '$exit += (s/ is an alias for .*// ||
	                        s/ is aliased to .*// ||
                                s/ is a function// ||
                                s/ is a shell function// ||
                                s/ is a shell builtin// ||
                                s/.* is hashed .(\S+).$/$1/ ||
                                s/.* is (a tracked alias for )?//);
                      END { exit not $exit }'
    }
    _warning_PAR() {
	echo "env_parallel: Warning: $*" >&2
    }
    _error_PAR() {
	echo "env_parallel: Error: $*" >&2
    }

    # Bash is broken in version 3.2.25 and 4.2.39
    # The crazy '[ "`...`" == "" ]' is needed for the same reason
    if [ "`_which_PAR parallel`" == "" ]; then
	# shellcheck disable=SC2016
	_error_PAR 'parallel must be in $PATH.'
	return 255
    fi

    # Grep regexp for vars given by --env
    # shellcheck disable=SC2006
    _grep_REGEXP="`_make_grep_REGEXP \"$@\"`"
    unset _make_grep_REGEXP

    # Deal with --env _
    # shellcheck disable=SC2006
    _ignore_UNDERSCORE="`_get_ignored_VARS \"$@\"`"
    unset _get_ignored_VARS

    # --record-env
    # Bash is broken in version 3.2.25 and 4.2.39
    # The crazy '[ "`...`" == 0 ]' is needed for the same reason
    if [ "`perl -e 'exit grep { /^--record-env$/ } @ARGV' -- "$@"; echo $?`" == 0 ] ; then
	true skip
    else
	(_names_of_ALIASES;
	 _names_of_FUNCTIONS;
	 _names_of_VARIABLES) |
	    cat > "$HOME"/.parallel/ignored_vars
	return 0
    fi

    # --session
    # Bash is broken in version 3.2.25 and 4.2.39
    # The crazy '[ "`...`" == 0 ]' is needed for the same reason
    if [ "`perl -e 'exit grep { /^--session$/ } @ARGV' -- "$@"; echo $?`" == 0 ] ; then
	true skip
    else
	# Insert ::: between each level of session
	# so you can pop off the last ::: at --end-session
	# shellcheck disable=SC2006
	PARALLEL_IGNORED_NAMES="`echo \"$PARALLEL_IGNORED_NAMES\";
          echo :::;
          (_names_of_ALIASES;
	   _names_of_FUNCTIONS;
	   _names_of_VARIABLES) | perl -ne '
	    BEGIN{
	      map { $ignored_vars{$_}++ }
                split/\s+/, $ENV{PARALLEL_IGNORED_NAMES};
	    }
	    chomp;
	    for(split/\s+/) {
	      if(not $ignored_vars{$_}) {
	        print $_,\"\\n\";
	      }
            }
	    '`"
	export PARALLEL_IGNORED_NAMES
	return 0
    fi
    # Bash is broken in version 3.2.25 and 4.2.39
    # The crazy '[ "`...`" == 0 ]' is needed for the same reason
    if [ "`perl -e 'exit grep { /^--end.?session$/ } @ARGV' -- "$@"; echo $?`" == 0 ] ; then
	true skip
    else
	# Pop off last ::: from PARALLEL_IGNORED_NAMES
	# shellcheck disable=SC2006
	PARALLEL_IGNORED_NAMES="`perl -e '
          $ENV{PARALLEL_IGNORED_NAMES} =~ s/(.*):::.*?$/$1/s;
	  print $ENV{PARALLEL_IGNORED_NAMES}
        '`"
	return 0
    fi
    # Grep alias names
    # shellcheck disable=SC2006
    _alias_NAMES="`_names_of_ALIASES | _remove_bad_NAMES | xargs echo`"
    _list_alias_BODIES="_bodies_of_ALIASES $_alias_NAMES"
    if [ "$_alias_NAMES" = "" ] ; then
	# no aliases selected
	_list_alias_BODIES="true"
    fi
    unset _alias_NAMES

    # Grep function names
    # shellcheck disable=SC2006
    _function_NAMES="`_names_of_FUNCTIONS | _remove_bad_NAMES | xargs echo`"
    _list_function_BODIES="_bodies_of_FUNCTIONS $_function_NAMES"
    if [ "$_function_NAMES" = "" ] ; then
	# no functions selected
	_list_function_BODIES="true"
    fi
    unset _function_NAMES

    # Grep variable names
    # shellcheck disable=SC2006
    _variable_NAMES="`_names_of_VARIABLES | _remove_bad_NAMES | xargs echo`"
    _list_variable_VALUES="_bodies_of_VARIABLES $_variable_NAMES"
    if [ "$_variable_NAMES" = "" ] ; then
	# no variables selected
	_list_variable_VALUES="true"
    fi
    unset _variable_NAMES

    _which_TRUE="`_which_PAR true`"
    # Copy shopt (so e.g. extended globbing works)
    # But force expand_aliases as aliases otherwise do not work
    PARALLEL_ENV="`
        _prefix_PARALLEL_ENV
        $_list_alias_BODIES;
        $_list_function_BODIES;
        $_list_variable_VALUES;
    `"
    export PARALLEL_ENV
    unset _list_alias_BODIES _list_variable_VALUES _list_function_BODIES
    unset _bodies_of_ALIASES _bodies_of_VARIABLES _bodies_of_FUNCTIONS
    unset _names_of_ALIASES _names_of_VARIABLES _names_of_FUNCTIONS
    unset _ignore_HARDCODED _ignore_READONLY _ignore_UNDERSCORE
    unset _remove_bad_NAMES _grep_REGEXP
    unset _prefix_PARALLEL_ENV
    # Test if environment is too big
    if [ "`_which_PAR true`" == "$_which_TRUE" ] ; then
	parallel "$@"
	_parallel_exit_CODE=$?
	# Clean up variables/functions
	unset PARALLEL_ENV
	unset _which_PAR _which_TRUE
	unset _warning_PAR _error_PAR
	# Unset _parallel_exit_CODE before return
	eval "unset _parallel_exit_CODE; return $_parallel_exit_CODE"
    else
	unset PARALLEL_ENV;
	_error_PAR "Your environment is too big."
	_error_PAR "You can try 3 different approaches:"
	_error_PAR "1. Run 'env_parallel --session' before you set"
	_error_PAR "   variables or define functions."
	_error_PAR "2. Use --env and only mention the names to copy."
	_error_PAR "3. Try running this in a clean environment once:"
	_error_PAR "     env_parallel --record-env"
	_error_PAR "   And then use '--env _'"
	_error_PAR "For details see: man env_parallel"
	return 255
    fi
}

parset() {
    _parset_PARALLEL_PRG=parallel
    _parset_main "$@"
}

env_parset() {
    _parset_PARALLEL_PRG=env_parallel
    _parset_main "$@"
}

_parset_main() {
    # If $1 contains ',' or space:
    #   Split on , to get the destination variable names
    # If $1 is a single destination variable name:
    #   Treat it as the name of an array
    #
    #   # Create array named myvar
    #   parset myvar echo ::: {1..10}
    #   echo ${myvar[5]}
    #
    #   # Put output into $var_a $var_b $var_c
    #   varnames=(var_a var_b var_c)
    #   parset "${varnames[*]}" echo ::: {1..3}
    #   echo $var_c
    #
    #   # Put output into $var_a4 $var_b4 $var_c4
    #   parset "var_a4 var_b4 var_c4" echo ::: {1..3}
    #   echo $var_c4

    _parset_NAME="$1"
    if [ "$_parset_NAME" = "" ] ; then
	echo parset: Error: No destination variable given. >&2
	echo parset: Error: Try: >&2
	echo parset: Error: ' ' parset myarray echo ::: foo bar >&2
	return 255
    fi
    if [ "$_parset_NAME" = "--help" ] ; then
	echo parset: Error: Usage: >&2
	echo parset: Error: ' ' parset varname GNU Parallel options and command >&2
	echo
	parallel --help
	return 255
    fi
    if [ "$_parset_NAME" = "--version" ] ; then
	# shellcheck disable=SC2006
	echo "parset 20230822 (GNU parallel `parallel --minversion 1`)"
	echo "Copyright (C) 2007-2023 Ole Tange, http://ole.tange.dk and Free Software"
	echo "Foundation, Inc."
	echo "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>"
	echo "This is free software: you are free to change and redistribute it."
	echo "GNU parallel comes with no warranty."
	echo
	echo "Web site: https://www.gnu.org/software/parallel"
	echo
	echo "When using programs that use GNU Parallel to process data for publication"
	echo "please cite as described in 'parallel --citation'."
	echo
	return 255
    fi
    shift

    # Bash: declare -A myassoc=( )
    # Zsh: typeset -A myassoc=( )
    # Ksh: typeset -A myassoc=( )
    # shellcheck disable=SC2039,SC2169
    if (typeset -p "$_parset_NAME" 2>/dev/null; echo) |
	    perl -ne 'exit not (/^declare[^=]+-A|^typeset[^=]+-A/)' ; then
	# This is an associative array
	# shellcheck disable=SC2006
	eval "`$_parset_PARALLEL_PRG -k --_parset assoc,"$_parset_NAME" "$@"`"
	# The eval returns the function!
    else
	# This is a normal array or a list of variable names
	# shellcheck disable=SC2006
	eval "`$_parset_PARALLEL_PRG -k --_parset var,"$_parset_NAME" "$@"`"
	# The eval returns the function!
    fi
}


# # This will call the functions above
# parallel -k echo ::: Put your code here
# env_parallel --session
# env_parallel -k echo ::: Put your code here
# parset p,y,c,h -k echo ::: Put your code here
# echo $p $y $c $h
# echo You can also activate GNU Parallel for interactive use by:
# echo . "$0"

env_parallel --session

mkdir -p tests2
mv tests/* tests2/ || true

cleanup () {
	rm tests/*
	mv tests2/* tests/
}
export PATH=$HOME/racket/bin:$PATH
trap cleanup EXIT
trap "exit 0" SIGHUP
fuzz() {
	pid=$1
	testname="tests/var${pid}_test_zfuzz"
	while true; do
		echo '#lang racket' >"${testname}.rkt"
		racket fuzz-smith.rkt --max-depth 25 --type-max-depth 25 >>"${testname}.rkt"
		reads=$(grep -o '(read)' "${testname}.rkt" | wc -l)
		touch "${testname}.in"
		for _ in $(seq 1 "$reads"); do
			echo $RANDOM >>"${testname}.in"
		done
		res="$(racket ${testname}.rkt <${testname}.in)"
		echo "$(( ((res % 256) + 256) % 256 ))" >"${testname}.res"
		tail -n +2 "${testname}.rkt" >"${testname}1.rkt"
		rm "${testname}.rkt" && mv "${testname}1.rkt" "${testname}.rkt"
		racket fuzz-test.rkt "var${pid}" 2>&1 | grep 'FAILURE' && break
		test "${PIPESTATUS[0]}" -eq 0 || break
		rm "${testname}.in"
	done
	echo "=== PROGRAM ==="
	cat "${testname}.rkt"
	echo "=== END PROGRAM ==="
	echo "=== INPUT ==="
	cat "${testname}.in"
	echo "=== END INPUT ==="
	echo "=== RES ==="
	cat "${testname}.res"
	echo "=== END RES ==="
	racket fuzz-test-debug.rkt "var${pid}"
	exit 1
}
export -f fuzz
np=$(nproc)
env_parallel --halt now,fail=1 fuzz ::: $(seq "$np")