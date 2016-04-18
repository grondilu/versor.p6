unit module Versor;

subset Metric of Array where { .all ~~ Real and .map(&abs).all == 1 }
subset Blade of Pair   where { .key ~~ UInt && .value ~~ Real }
sub blade returns Blade { $^a => $^b }

role Basis {
    method Str(UInt $b is copy:) {
	return 's' unless $b;
	my int $n = 0;
	join '∧', map { "e$_" },
	gather while $b > 0 {
	    $n++;
	    take $n if $b +& 1;
	    $b +>= 1;
	}
    }
}

# Type of multivector.
# A type has a name, it lies on a basis,
# and an instance has an array of coordinates
# in that basis.
role Type {
    has $.key;
    has Str  $.name;
    has Str  $.alias is rw;
    has Basis @.basis;
    has Real @.coord;
    has Bool $.generated = False;
    has Bool $.dual = False;
}

sub grade(UInt $b is copy --> UInt) {
    my int $n = 0;
    while $b > 0 {
	if $b +& 1 { $n++ }
	$b +>= 1;
    }
    return $n;
}
sub sign(UInt $a, UInt $b --> Int) {
    my int $n = $a +> 1;
    my $sum = 0;
    while $n > 0 {
	$sum += grade($n +& $b);
	$n +>= 1;
    }
    return $sum +& 1 ?? -1 !! +1;
}
sub product(UInt $a, UInt $b) returns Blade { blade($a +^ $b, sign($a, $b)) }
sub outer(UInt $a, UInt $b)   returns Blade { $a +& $b ?? blade(0, 0) !! product($a, $b) }
sub involute(UInt $x)         returns Blade { blade($x, (-1)**grade($x)) }
sub reverse(UInt $x)          returns Blade { blade($x, (-1)**($_*($_-1) div 2)) given grade($x) }
sub conjugate(UInt $x)        returns Blade { blade($x, (-1)**($_*($_+1) div 2)) given grade($x) }
sub basisString(UInt $b is copy) returns Str {
    return 's' unless $b;
    my int $n = 0;
    join '∧', map { "e$_" },
    gather while $b > 0 {
	$n++;
	take $n if $b +& 1;
	$b +>= 1;
    }
}
sub basisBit(Str $name) returns UInt {
    return 0 if $name eq 's';
    ([+] map { 1 +< ($_ - 1) }, $name.comb(/\d/)) but Basis;
}
sub keyCheck($k1, $k2) returns Bool {
    $k1.elems == $k2.elems and [&&] $k1 Z~~ $k2
}

sub order($c) {
    my $tblades = [ ^$c.elems ];
    # tblades.=sort; # useless?
    return { :blades($tblades), :inst($c) }
}
sub compress($x) {...}

our class Space {

    our role Conformal {...}

    has Metric $.metric = [1, 1, 1];
    # Normally the plural of 'basis' is 'bases' but meh,
    # I don't want to confuse things.  From now on I'll assume
    # the word designate both a basis multivector (e.g. e1∧e3)
    # and the basis (as in 'linear basis') of a multivector space.
    has Basis  @.basis;
    has Type   %!types;

    has $!values;

    has %!products;
    has @!subspaces;

    has $!api;

    submethod BUILD(:$metric, :$conformal, :$types) {
	$!metric //= $metric;
	self does Conformal if $conformal;

	@!basis  = self.buildBasis();
	%!types  = self.buildTypes();

	%!products = self.buildProducts();
	@!subspaces = self.buildSubspaces();
	self.registerSubspaces();

	self.createTypes($types) if $types;

	#$!api = self.generate($props);
    }

    method buildBasis {
	my @basis = 0;
	my %basis; %basis{0}++;

	# build the coordinate blades (e1, e2, e3, ...)
	push @basis, slip (1, 2, 4 ... *)[^$!metric];
	%basis{@basis}»++;

	# build the bivectors (e12, e23, ...)
	for @basis -> $i {
	    for @basis -> $j {
		if $i !== $j {
		    my $r = outer($i, $j);
		    push @basis, $r.key unless %basis{$r.key}++;
		}
	    }
	}
	die 'unexpected basis size' unless @basis == 2**$!metric;
	return
	map { $_ but Basis },
	sort {
	    grade($^a) <=> grade($^b) ||
	    $a <=> $b
	}, @basis;
    }
    method buildTypes {
	my %types;
	for @!basis -> $b {
	    my $key = self.key($b);
	    my $name = ~$b;
	    %types{$name} = Type.new:
	    :$key,
	    :basis(my Basis @ = $b),
	    :$name;
	}
	return %types;
    }
    method buildProducts {
	my %table;
	for @!basis -> $a {
	    for @!basis -> $b {
		%table<gp>[$a][$b] = self.metricProduct($a, $b);
		%table<ip>[$a][$b] = self.metricInner($a, $b);
		%table<op>[$a][$b] = outer($a, $b);
	    }
	}
	return %table;
    }
    method buildSubspaces {
	my @subspaces = 1, |map {
	    (
		name => <Vec Biv Tri Quad Penta Hexa Hepta Octo>[$_],
		basis => my Basis @
	    ).Hash
	}, ^$!metric;
	for @!basis[1..*] -> $b {
	    my $grade = grade($b);
	    last if $grade > $!metric;
	    push @subspaces[$grade]<basis>, $b;
	}
	return @subspaces;
    }
    method registerSubspaces {
	for @!subspaces[1..*] -> $subspace {
	    %!types{$subspace<name>} = Type.new:
	    :key(self.basesKey($subspace<basis>)),
	    :name($subspace<name>),
	    :basis(|$subspace<basis>)
	    ;
	}
    }
    method createTypes($types) {
	for @$types -> $type {
	    my $name = $type.key;
	    my Basis @basis = map &basisBit, |$type.value;
	    self.createType(@basis, $name);
	}
    }
    method createType(Basis @basis, Str $name, Bool :$aliasExisting) {
	my $key = self.basesKey(@basis);
	for %!types {
	    if keyCheck($key, .value.key) {
		if $aliasExisting {
		    self.aliasType(.value.name, $name);
		    return $name;
		} else {
		    return .value.name;
		}
	    }
	}
	%!types{$name} = Type.new: :$key, :$name, :@basis;
    }
    method aliasType($oldname, $newname) {
	%!types{$newname} = %!types{$oldname};
	%!types{$oldname}.alias = $newname;
    }
    method metricProduct(UInt $a, UInt $b) {
	my $tmp = product($a, $b);
	my $w = $tmp.value;
	my $bs = $a +& $b;
	my int $i = 1;
	while $bs > 0 {
	    $w *= $!metric[$i-1] if $bs +& 1;
	    $bs +>= 1;
	    $i++;
	}
	return $tmp.key => $w;
    }
    method metricInner(UInt $a, UInt $b) {
	my $tmp = self.metricProduct($a, $b);
	my $g = grade($b) - grade($a);
	if grade($a) > grade($b) or grade($tmp.key) !== $g {
	    return blade(0, 0);
	} else {
	    return $tmp;
	}
    }
    method key(Int $b?) {
	my $nkeys = (@!basis/32).ceiling;
	my $key = [0 xx $nkeys];
	if $b.defined {
	    my $k = (($b + 1)/32).ceiling;
	    my $shft = ($b+1) - 32 * ($k - 1);
	    $key[$k-1] = 1 +< ($shft - 1);
	}
	return $key;
    }
    method basesKey(Basis @basis) {
	my $key = self.key();
	for ^@basis -> $i {

	    my $b = @basis[$i];
	    my $ty = %!types{~$b};
	    for ^$ty.key -> $k {
		$key[$k] +|= $ty.key[$k];
	    }
	}
	return $key;
    }
    method generate($props) {...}

    role Conformal {
	has ($.no, $.ni, $.ep, $.em, $.eplane);
	submethod BUILD {
	    die 'undefined basis' unless self.basis.defined;
	    $!no = 1 +< (self.metric - 2);
	    $!ni = 1 +< (self.metric - 1);
	    $!ep = $!no;
	    $!em = $!ni;
	    $!eplane = $!no +| $!ni;
	}
	method buildProducts {...}
    }

}
