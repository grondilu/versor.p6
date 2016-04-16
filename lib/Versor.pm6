unit module Versor;
use MONKEY-SEE-NO-EVAL;

INIT die 'This is work in progress.  Do not run yet!';
#subset Metric of Array where { .all ~~ Real and .map(&abs).all == 1 }
sub foreach($t, &f) {
    loop (my int $i; $i < $t.elems; $i++) { &f($t[$i], $i) }
}
sub blade(UInt $id, Real $w) returns Hash { { :$id, :$w } }

sub type($key, $bases, $name) returns Hash {
    { :$key, :$bases, :$name, :generated, :!dual }
}

sub classname(Str $name --> Str) { "_$name" }
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
sub product(UInt $a, UInt $b) { blade($a +^ $b, sign($a, $b)) }
sub outer(UInt $a, UInt $b)   { $a +& $b ?? blade(0, 0) !! product($a, $b) }
sub involute(UInt $x)         { blade($x, (-1)**grade($x)) }
sub reverse(UInt $x)          { blade($x, (-1)**($_*($_-1) div 2)) given grade($x) }
sub conjugate(UInt $x)        { blade($x, (-1)**($_*($_+1) div 2)) given grade($x) }
sub basisString(UInt $b is copy) returns Str {
    my int $n = 0;
    my Str $res;
    while $b > 0 {
	$n++;
	$res ~= $n if $b +& 1;
	$b +>= 1;
    }
    $n > 0 ?? "e$res" !! 's';
}
sub basisBit(Str $name) returns UInt {
    return 0 if $name eq 's';
    my int $x = 0;
    [+] map { 1 +< ($_ - 1) }, $name.comb(/\d/);
}

sub basisBits { map &basisBit, @_ }
sub basisNames { map &basisString, sort @_ }
sub keyCheck($k1, $k2) returns Bool {
    $k1.elems == $k2.elems and [&&] $k1 Z~~ $k2
}

sub order($c) {
    my $tblades = [ ^$c.elems ];
    # tblades.=sort; # useless?
    return { :blades($tblades), :inst($c) }
}
sub compress($x) {
    $x
    .map({ Pair.new: .<id>, .<w> })
    .MixHash
    .pairs
    .map({blade(.key, .value)})
}
sub printLines(Str $text) { print $text.subst(/^^/, {"{$++}: "}, :g) }

our class Space {
    has $.metric;
    has $.basis;
    has $.types;

    has $!values;
    has $!products;
    has $!subspaces;
    has $!api;

    has Bool $.initialized;

    submethod BUILD(:$props) {
	$props<metric> //= [ 1, 1, 1 ];
	$props<types>  //= [];
	$props<binops> //= [];

	$!metric = $props<metric>;
	$!basis  = self.buildBasis();
	$!types  = self.buildTypes();
	if $props<conformal> {
	    $!values = self.buildConformalValues();
	    $!products = self.buildConformal();
	} else {
	    $!products = self.buildEuclidean();
	}
	$!subspaces = self.buildSubspaces();
	self.registerSubspaces();
	self.createTypes($props<types>);

	$!api = self.generate($props);
	method AT-KEY($name) { self.api.constructors{$name} }
	$!initialized = True;
    }

    method generate($props) {
	my $binopCode = self.generateBinops($props<binops>);
	my $typeCode = self.generateRegisteredTypes();
	my $typeCodeAliases;
	for $typeCode.keys -> $name {
	    my $ty = $!types{$name};
	    if $ty<alias> && $name eq $ty<alias> {
		$typeCodeAliases{$name} = $typeCode{$name};
	    }
	}

	my $functionBody = [ 'my $api = { classes => {}, constructors => {} };' ];
	for $typeCode.keys -> $name {
	    if !$typeCodeAliases{$name} {
		my $code = $typeCode{$name};
		$functionBody.push: [
		    $code,
		    '$api<constructors>{' ~$name~ '} = ' ~$name~ ';',
		    '$api<classes>{' ~$name~ '} = ' ~ classname($name) ~';',
		].join("\n");
		if $!types{$name}<alias> {
		    my $aliasName = $!types{$name}<alias>;
		    my $aliasCode = $typeCodeAliases{$aliasName};
		    $functionBody.push: [
			$aliasCode,
			'$api<constructors>{' ~ $aliasName ~ '} = ' ~ $aliasName ~ ';',
			'$api<classes>{' ~$aliasName~ '} = ' ~ classname($aliasName) ~';',
		    ].join("\n");
		}
	    }
	}
	$functionBody = [flat @$functionBody, @$binopCode];
	$functionBody.push('return $api;');
	my &f = EVAL 'sub ($space) '~"\x7B" ~ $functionBody.join("\n\n") ~ "\x7D";
	return f(self);
    }

    method metricProduct(UInt $a, UInt $b) {
	my $tmp = product($a, $b);
	my $bs = $a +& $b;
	my int $i = 1;
	while $bs > 0 {
	    $tmp<w> *= $!metric[$i-1] if $bs +& 1;
	    $bs +>= 1;
	    $i++;
	}
	return $tmp;
    }

    method metricInner(UInt $a, UInt $b) {
	my $tmp = self.metricProduct($a, $b);
	my $g = grade($b) - grade($a);
	if grade($a) > grade($b) or grade($tmp<id>) !== $g {
	    return blade(0, 0);
	} else {
	    return $tmp;
	}
    }

    method key(UInt $b?) {
	my $nkeys = ($!basis/32).ceiling;
	my $key = [0 xx $nkeys];
	if $b.defined {
	    my $k = (($b + 1)/32).ceiling;
	    my $shft = ($b+1) - 32 * ($k - 1);
	    $key[$k-1] = 1 +< ($shft - 1);
	}
	return $key;
    }

    method basesKey($bases) {
	my $key = self.key();
	for ^$bases.elems -> $i {
	    my $b = $bases[$i];
	    my $ty = $!types{basisString($b)};
	    for ^$ty<key>.elems -> $k {
		$key[$k] +|= $ty<key>[$k];
	    }
	}
	return $key;
    }

    method buildBasis {
	my $basis = [0];
	my $basisMap = {0 => True};

	# build the coordinate blades (e1, e2, e3, ...)
	my int $nb = 1;
	for ^$!metric.elems {
	    push $basis, $nb;
	    $basisMap{$nb} = True;
	    $nb +<= 1;
	}
	# build the bivectors (e12, e23, ...)
	for ^$basis.elems -> $i {
	    for ^$basis.elems -> $j {
		if $i !== $j {
		    my $r = outer($basis[$i], $basis[$j]);
		    if $r<id> !== 0 and !$basisMap{$r<id>} {
			push $basis, $r<id>;
			$basisMap{$r<id>} = True;
		    }
		}
	    }
	}
	return sort {
	    grade($^a) <=> grade($^b) ||
	    $^a <=> $^b
	}, $basis;
    }

    method buildTypes {
	my $types = {};
	for ^$!basis.elems -> $i {
	    my $b = $!basis[$i];
	    my $key = self.key($b);
	    my $name = basisString($b);
	    $types{$name} = type( :$key, :bases($!basis), :$name );
	}
	return $types;
    }

    method bladeTable {
	my $S = {};
	for ^$!basis.elems -> $i {
	    my $b = $!basis[$i];
	    my $name = basisString($b);
	    $S{$b} = {
		:id($name),
		:basis($b),
		:gp({}), :op({}), :ip({})
	    };
	}
	return $S;
    }

    method checkMink($x) {
	my $v = $x +& $!values<eplane>;
	if $v == 0 || $v == $!values<eplane> {
	    return False;
	} else {
	    return True;
	}
    }

    method buildEuclidean {
	my $S = self.bladeTable();
	for ^$!basis.elems -> $i {
	    my $iv = $!basis[$i];
	    for ^$!basis.elems -> $j {
		my $jv = $!basis[$j];
		my $gp = self.metricProduct($iv, $jv);
		my $op = outer($iv, $jv);
		my $ip = self.metricInner($iv, $jv);

		$S{$iv}<gp>{$jv} = [$gp];
		$S{$iv}<op>{$jv} = [$op];
		$S{$iv}<ip>{$jv} = [$ip];
		$S{$iv}<involute>  = involute($iv);
		$S{$iv}<reverse>   = reverse($iv);
		$S{$iv}<conjugate> = conjugate($iv);
	    }
	}
	return $S;
    }

    method pushMink($x) {
	if $x +& $!values<no> == $!values<no> {
	    my $t = $x +^ $!values<no>;
	    return [
		blade($t +^ $!values<ep>, .5),
		blade($t +^ $!values<em>, .5)
	    ];
	} elsif $x +& $!values<ni> == $!values<ni> {
	    my $t = $x +^ $!values<ni>;
	    return [
		blade($t +^ $!values<ep>, -1),
		blade($t +^ $!values<em>, 1)
	    ];
	}
    }

    method popMink($x) {
	if $x +& $!values<ep> == $!values<ep> {
	    my $t = $x +^ $!values<ep>;
	    return [
		blade($t +^ $!values<no>, 1),
		blade($t +^ $!values<ni>, -.5),
	    ];
	} elsif $x +& $!values<em> == $!values<em> {
	    my $t = $x +^ $!values<em>;
	    return [
		blade($t +^ $!values<no>, 1),
		blade($t +^ $!values<ni>, .5)
	    ];
	}
    }

    method accumMink($blades) {
	my $res = [];
	for ^$blades.elems -> $i {
	    my $iv = $blades[$i];
	    if self.checkMink($iv<id>) {
		my $minkBlades = self.popMink($iv<id>);
		for ^$minkBlades -> $j {
		    my $jv = $minkBlades[$j];
		    $jv<w> *= $iv<w>;
		}
		$res.push: slip $minkBlades;
	    } else {
		$res.push: $iv;
	    }
	}
	return $res;
    }

    method buildConformalBinop($S, $iv, $jv) {
	my $tmpA = self.checkMink($iv) ?? self.pushMink($iv) !! [blade($iv, 1)];
	my $tmpB = self.checkMink($jv) ?? self.pushMink($jv) !! [blade($jv, 1)];

	my $gpTally = [];
	my $opTally = [];
	my $ipTally = [];
	for ^$tmpA.elems -> $a {
	    my $av = $tmpA[$a];
	    for ^$tmpB.elems -> $b {
		my $bv = $tmpB[$b];
		my $gp = self.metricProduct($av<id>, $bv<id>);
		my $op = outer($av<id>, $bv<id>);
		my $ip = self.metricInner($av<id>, $bv<id>);

		$gpTally.push(blade($gp<id>, $gp<w>*$av<w>*$bv<w>));
		$opTally.push(blade($op<id>, $op<w>*$av<w>*$bv<w>));
		$ipTally.push(blade($ip<id>, $ip<w>*$av<w>*$bv<w>));
	    }
	}

	my $gpPop = self.accumMink(compress($gpTally));
	my $opPop = self.accumMink(compress($opTally));
	my $ipPop = self.accumMink(compress($ipTally));

	$S[$iv]<gp>[$jv] = compress($gpPop);
	$S[$iv]<op>[$jv] = compress($opPop);
	$S[$iv]<ip>[$jv] = compress($ipPop);
    }

    method buildConformalValues {
	my $no = 1 +< ($!metric.elems - 2);
	my $ni = 1 +< ($!metric.elems - 1);
	return {
	    :$no, :$ni
	    :ep($no), :em($ni),
	    :eplane($no +| $ni)
	}
    }

    method buildConformal {
	my $S = self.bladeTable();
	for ^$!basis.elems -> $i {
	    my $ib = $!basis{$i};
	    $S{$ib}<involute>  = involute($ib);
	    $S{$ib}<reverse>   = reverse($ib);
	    $S{$ib}<conjugate> = conjugate($ib);

	    for ^$!basis.elems -> $j {
		my $jb = $!basis[$j];
		self.buildConformalBinop($S, $ib, $jb);
	    }
	}
	return $S;
    }

    my $_subspaceNames = <Vec Biv Tri Quad Penta Hexa Hepta Octo>;

    method buildSubspaces {
	my $subspaces = [];
	for ^$!metric.elems -> $i {
	    $subspaces[$i] = {
		name => $_subspaceNames[$i],
		bases => []
	    };
	}

	for ^$!basis.elems -> $i {
	    my $b = $!basis[$i];
	    my $g = grade($b);
	    if $g > 0 {
		my $bases = $subspaces[$g-1]<bases>;
		$bases.push: $b;
	    }
	}
	return $subspaces;
    }

    method registerSubspaces {
	for ^$!subspaces.elems -> $i {
	    my $iv = $!subspaces[$i];
	    $!types{$iv<name>} = type(
		self.basesKey($iv<bases>, $iv<base>, $iv<name>)
	    );
	}
    }

    method aliasType($oty, $nty) {
	$!types{$nty} = $!types{$oty};
	$!types{$oty}<alias> = $nty;
=begin comment
	    //this.types[oty].alias = nty
	    /*delete this.types[oty];
	    
	    // rename subspace if necessary
	    for(var i=0; i < this.subspaces.length; ++i) {
		    var subs = this.subspaces[i];
		    if(subs.name == oty) {
			    subs.name = nty
			    break;
		    }
	    }
	    */
=end comment
    }

    method createType($bases, $name, $aliasExisting) {
	my $key = self.basesKey($bases);
	for $!types.keys -> $tyname {
	    my $ty = $!types{$tyname};
	    if keyCheck($key, $ty<key>) {
		if $aliasExisting {
		    self.aliasType($tyname, $name);
		    return $name;
		} else {
		    return $tyname;
		}
	    }
	}
	$!types{$name} = type($key, $bases, $name);
	return $name;
    }


    method productList($bases1, $bases2, $opname) {
	my $tally = [];

	my $idx = 0;
	for ^$bases1.elems -> $i {
	    my $iv = $bases1[$i];
	    for ^$bases2.elems -> $j {
		my $jv = $bases2[$j];

		my $prod = $!products[$iv]{$opname}[$jv];
		for ^$prod.elems -> $k {
		    my $instruction = {
			:a($i), :b($j),
			:ida(basisString($iv)),
			:idb(basisString($jv)),
			:r($prod[$k])
		    };
		    $tally[$idx] = $instruction;
		    $idx++;
		}
	    }
	}

	my $combined = {};
	for ^$tally.elems -> $i {
	    my $instruction = $tally[$i];
	    if $instruction<r><w> == 0 { next }

	    my $b = $instruction<r><id>;
	    if $combined{$b} {
		my $instructions = $combined{$b};
		$instructions.push: $instruction;
	    } else {
		$combined{$b} = [$instruction];
	    }
	}
	return order($combined);
    }

    method generateType($name) {
	my $ty = $!types{$name};
	my $coords = basisNames($ty<bases>);

	my $getfields = [];
	my $setfields = [];
	foreach($coords, sub ($v, $i) {
	    $getfields[$i] = "self\{$i\}";
	    $setfields[$i] = "$getfields[$i] = $v";
	});

	my $model = {
	    :$name,  :classname(classname($name)),
	    :parameters($coords.join(', ')),
	    :$coords,
	    :getfields($getfields.join(', ')),
	    :$setfields,
	    :isdual($ty<dual>),
	};
	my $create = [
	    "my $model<name> = sub ($model<parameters>) \{",
	    "\treturn "~$model<classname>~'.new('~$model<parameters>~');',
	    "\}"
	].join("\n");

       # TODO:  THIS IS GROSSLY INCOMPLETE
       my $def = [
	   'class '~$model<classname>~ '{',
	   "\t" ~ $model<parameters>,
	   $model<setfields>.join("\n"),
	   '}',
	   ''
       ].join("\n");

       my $code = [$def];

       $code.push(self.generateUnop('reverse'  , $name));
       $code.push(self.generateUnop('involute' , $name));
       $code.push(self.generateUnop('conjugate', $name));
       $code.push($create);

       $ty.generated = True;

       return $code.join("\n\n");
   }

   method createCast($toName, $fromName) {
       my $toTy = $!types{$toName};
       my $fromTy = $!types{$fromName};

       my $fromCoordMap = {};
       foreach($fromTy<bases>, sub ($v, $i) {
	   $fromCoordMap{$v} = $i;
       });

       my $ops = [];
       foreach($toTy<bases>, sub ($v, $i) {
	   my $src;
	   if $fromCoordMap{$v} ~~ Real { $src = '$b[' ~$fromCoordMap{$v}~']' }
	   else { $src = '0' }
	   $ops[$i] = "self[$i] = $src;";
       });

       my $model = {
	   :classname(classname($toName)),
	   :fromTy($fromName),
	   :ops($ops.join("\n"))
       };

       # TODO!
       my $code = [
	   '# method ' ~ $model<classname> ~ '::' ~ $model<fromTy> ~ '{...}',
       ].join("\n");

       my &f = EVAL "sub ({classname($toName)}) \x7B $code \x7D";
       f($!api<classes>{$toName});
   }

   method generateUnop($opname, $tyname) {
       my $ty = $!types{$tyname};
       my $coords = basisNames($ty<bases>);

       my $_this = self;
       my $ops = [];
       foreach($ty<bases>, sub ($v, $i) {
	   my $blade = $_this.products{$v}{$opname};
	   $ops[$i] = (($blade<w> > 0) ?? '' !! '-') ~ "self\{$i\}";
       });
       
       my $model = {
	   :classname(classname($tyname)),
	   :$opname,
	   :ops($ops.join(", "))
       };
       return [
	   "method $model<classname>::$model<opname> \{",
	   "\}"
       ].join("\n");
   }

   method binopResultType($opname, $tyname1, $tyname2) {
       my $ty1 = $!types{$tyname1};
       my $ty2 = $!types{$tyname2};

       my $op = self.productList($ty1<bases>, $ty2<hases>, $opname);
       my $tynameRes;
       if $op<blades>.elems == 0 {
	   $tynameRes = 's';
       } else {
	   $tynameRes = self.createTypes(
	       $op<blades>,
	       "$tyname1$tyname2"~ "_$opname",
	       False
	   );
       }
       return $tynameRes;
   }

   method generateBinop($opname, $tyname1, $tyname2) {
       my $ty1 = $!types{$tyname1};
       my $ty2 = $!types{$tyname2};

       my $op = self.productList($ty1<bases>, $ty2<bases>, $opname);
       my $tynameRes = self.binopResultType($opname, $tyname1, $tyname2);

       my $tyRes = $!types{$tynameRes};
       if !$tyRes {
	   warn "Error: gentype $tyname1{$tyname2}_$opname, ", $op<blades>;
       } elsif $!initialized && !$tyRes<generated> {
	   ...
       }
       ...
   }

    method createBinop($opname, $tyname1, $tyname2) {
	...
    }

    method createAffineOp($opname, $tyname1, $tyname2) {
	...
    }

    method generateRegisteredTypes {
	...
    }

    method createTypes($types) {
	...
    }

    method ip($a, $b) { $a.ip($b) }
    method op($a, $b) { $a.op($b) }
    method gp($a, $b) {...}
    method sp($a, $b) { $a.sp($b) }
    method isSubType($tyname1, $tyname2) {
	...
    }
}

our sub create($props) { Space.new: :$props }
