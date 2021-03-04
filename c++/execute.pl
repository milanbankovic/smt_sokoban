#!/usr/bin/perl -w

use Time::HiRes qw(gettimeofday);

if($#ARGV < 1)
{
  print "usage: $0 input_file limit\n";
  exit;
}

$input_file = $ARGV[0];
$limit = $ARGV[1];
$found = 0;

$start_time = Time::HiRes::gettimeofday();


for($len = 0; $len <= $limit && $found == 0; $len++)
{
    $instance_start_time = Time::HiRes::gettimeofday();
    print "Length $len:\n";
    system("./generate_bv $input_file ${input_file}_${len}.smt2 $len 2> /dev/null");
    system("./z3 ${input_file}_${len}.smt2 > ${input_file}_${len}.out 2> /dev/null");
    open(RES, "${input_file}_${len}.out") or die "Cannot open ${input_file}_${len}.out\n";

    @content = <RES>;
    $content = join("", @content);
    close(RES);
    if($content =~ "unsat")
    {
	print "No plan of length $len\n";
    }
    else
    {
	print "SUCCESS: Found plan of length: $len\n";
	print "Verifying solution...\n";
	system("cat ${input_file}_${len}.out | grep -o -E '#b[0-1][0-1][0-1]?' > ${input_file}_${len}.moves");
	system("./check_bv $input_file ${input_file}_${len}.moves > ${input_file}_${len}.res");
	$found = 1;
	$instance_time = Time::HiRes::gettimeofday() - $instance_start_time;
	$cumulative_time = Time::HiRes::gettimeofday() - $start_time;

	print "Instance time for length $len: ".$instance_time."s\n";
	print "Cumulative time for length $len: ".$cumulative_time."s\n";	
    }
    unlink("${input_file}_${len}.smt2");
    unlink("${input_file}_${len}.out");
    unlink("${input_file}_${len}.moves");
}

