(get-info :version)
; (:version "4.5.1")
; Started: 2017-09-29 12:25:11
; Silicon.buildVersion: 1.1-SNAPSHOT 5209e6ef33c3 default 2017/09/28 17:15:19
; Input file: null
; Verifier id: 00
; ------------------------------------------------------------
; Begin preamble
; ////////// Static preamble
; 
; ; /z3config.smt2
; (set-option :print-success true) ; Boogie: false
(set-option :global-decls true) ; Boogie: default
(set-option :auto_config false) ; Usually a good idea
(set-option :smt.mbqi false)
(set-option :model.v2 true)
(set-option :smt.phase_selection 0)
(set-option :smt.restart_strategy 0)
(set-option :smt.restart_factor |1.5|)
(set-option :smt.arith.random_initial_value true)
(set-option :smt.case_split 3)
(set-option :smt.delay_units true)
(set-option :smt.delay_units_threshold 16)
(set-option :nnf.sk_hack true)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :type_check true)
(set-option :smt.bv.reflect true)
; 
; ; /preamble.smt2
(declare-datatypes () ((
    $Snap ($Snap.unit)
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
(declare-sort $Ref 0)
(declare-const $Ref.null $Ref)
(define-sort $Perm () Real)
(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)
(define-fun $Perm.isValidVar ((p $Perm)) Bool
	(<= $Perm.No p))
(define-fun $Perm.isReadVar ((p $Perm) (ub $Perm)) Bool
    (and ($Perm.isValidVar p)
         (not (= p $Perm.No))
         (< p $Perm.Write)))
(define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))
(define-fun $Math.min ((a Int) (b Int)) Int
    (ite (<= a b) a b))
(define-fun $Math.clip ((a Int)) Int
    (ite (< a 0) 0 a))
; ////////// Sorts
(declare-sort $Seq<$Ref>)
(declare-sort $Seq<Int>)
(declare-sort Set<$Ref>)
(declare-sort Set<Int>)
(declare-sort $FVF<$Ref>)
(declare-sort $FVF<Int>)
(declare-sort Set<$Snap>)
(declare-sort $PSF<$Snap>)
; ////////// Sort wrappers
; Declaring additional sort wrappers
(declare-fun $SortWrappers.IntTo$Snap (Int) $Snap)
(declare-fun $SortWrappers.$SnapToInt ($Snap) Int)
(assert (forall ((x Int)) (!
    (= x ($SortWrappers.$SnapToInt($SortWrappers.IntTo$Snap x)))
    :pattern (($SortWrappers.IntTo$Snap x))
    :qid |$Snap.Int|
    )))
(declare-fun $SortWrappers.BoolTo$Snap (Bool) $Snap)
(declare-fun $SortWrappers.$SnapToBool ($Snap) Bool)
(assert (forall ((x Bool)) (!
    (= x ($SortWrappers.$SnapToBool($SortWrappers.BoolTo$Snap x)))
    :pattern (($SortWrappers.BoolTo$Snap x))
    :qid |$Snap.Bool|
    )))
(declare-fun $SortWrappers.$RefTo$Snap ($Ref) $Snap)
(declare-fun $SortWrappers.$SnapTo$Ref ($Snap) $Ref)
(assert (forall ((x $Ref)) (!
    (= x ($SortWrappers.$SnapTo$Ref($SortWrappers.$RefTo$Snap x)))
    :pattern (($SortWrappers.$RefTo$Snap x))
    :qid |$Snap.$Ref|
    )))
(declare-fun $SortWrappers.$PermTo$Snap ($Perm) $Snap)
(declare-fun $SortWrappers.$SnapTo$Perm ($Snap) $Perm)
(assert (forall ((x $Perm)) (!
    (= x ($SortWrappers.$SnapTo$Perm($SortWrappers.$PermTo$Snap x)))
    :pattern (($SortWrappers.$PermTo$Snap x))
    :qid |$Snap.$Perm|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$Seq<$Ref>To$Snap ($Seq<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Seq<$Ref> ($Snap) $Seq<$Ref>)
(assert (forall ((x $Seq<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$Seq<$Ref>($SortWrappers.$Seq<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$Seq<$Ref>To$Snap x))
    :qid |$Snap.$Seq<$Ref>|
    )))
(declare-fun $SortWrappers.$Seq<Int>To$Snap ($Seq<Int>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Seq<Int> ($Snap) $Seq<Int>)
(assert (forall ((x $Seq<Int>)) (!
    (= x ($SortWrappers.$SnapTo$Seq<Int>($SortWrappers.$Seq<Int>To$Snap x)))
    :pattern (($SortWrappers.$Seq<Int>To$Snap x))
    :qid |$Snap.$Seq<Int>|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.Set<$Ref>To$Snap (Set<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapToSet<$Ref> ($Snap) Set<$Ref>)
(assert (forall ((x Set<$Ref>)) (!
    (= x ($SortWrappers.$SnapToSet<$Ref>($SortWrappers.Set<$Ref>To$Snap x)))
    :pattern (($SortWrappers.Set<$Ref>To$Snap x))
    :qid |$Snap.Set<$Ref>|
    )))
(declare-fun $SortWrappers.Set<Int>To$Snap (Set<Int>) $Snap)
(declare-fun $SortWrappers.$SnapToSet<Int> ($Snap) Set<Int>)
(assert (forall ((x Set<Int>)) (!
    (= x ($SortWrappers.$SnapToSet<Int>($SortWrappers.Set<Int>To$Snap x)))
    :pattern (($SortWrappers.Set<Int>To$Snap x))
    :qid |$Snap.Set<Int>|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$FVF<$Ref>To$Snap ($FVF<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<$Ref> ($Snap) $FVF<$Ref>)
(assert (forall ((x $FVF<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<$Ref>($SortWrappers.$FVF<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$FVF<$Ref>To$Snap x))
    :qid |$Snap.$FVF<$Ref>|
    )))
(declare-fun $SortWrappers.$FVF<Int>To$Snap ($FVF<Int>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<Int> ($Snap) $FVF<Int>)
(assert (forall ((x $FVF<Int>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<Int>($SortWrappers.$FVF<Int>To$Snap x)))
    :pattern (($SortWrappers.$FVF<Int>To$Snap x))
    :qid |$Snap.$FVF<Int>|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.Set<$Snap>To$Snap (Set<$Snap>) $Snap)
(declare-fun $SortWrappers.$SnapToSet<$Snap> ($Snap) Set<$Snap>)
(assert (forall ((x Set<$Snap>)) (!
    (= x ($SortWrappers.$SnapToSet<$Snap>($SortWrappers.Set<$Snap>To$Snap x)))
    :pattern (($SortWrappers.Set<$Snap>To$Snap x))
    :qid |$Snap.Set<$Snap>|
    )))
(declare-fun $SortWrappers.$PSF<$Snap>To$Snap ($PSF<$Snap>) $Snap)
(declare-fun $SortWrappers.$SnapTo$PSF<$Snap> ($Snap) $PSF<$Snap>)
(assert (forall ((x $PSF<$Snap>)) (!
    (= x ($SortWrappers.$SnapTo$PSF<$Snap>($SortWrappers.$PSF<$Snap>To$Snap x)))
    :pattern (($SortWrappers.$PSF<$Snap>To$Snap x))
    :qid |$Snap.$PSF<$Snap>|
    )))
; ////////// Symbols
(declare-fun Set_equal (Set<Int> Set<Int>) Bool)
(declare-fun Set_subset (Set<Int> Set<Int>) Bool)
(declare-fun Set_intersection (Set<Int> Set<Int>) Set<Int>)
(declare-fun Set_difference (Set<Int> Set<Int>) Set<Int>)
(declare-fun Set_disjoint (Set<Int> Set<Int>) Bool)
(declare-fun Set_union (Set<Int> Set<Int>) Set<Int>)
(declare-fun Set_unionone (Set<Int> Int) Set<Int>)
(declare-fun Set_singleton (Int) Set<Int>)
(declare-const Set_empty Set<Int>)
(declare-fun Set_card (Set<Int>) Int)
(declare-fun Set_in (Int Set<Int>) Bool)
(declare-fun Set_equal (Set<$Ref> Set<$Ref>) Bool)
(declare-fun Set_subset (Set<$Ref> Set<$Ref>) Bool)
(declare-fun Set_intersection (Set<$Ref> Set<$Ref>) Set<$Ref>)
(declare-fun Set_difference (Set<$Ref> Set<$Ref>) Set<$Ref>)
(declare-fun Set_disjoint (Set<$Ref> Set<$Ref>) Bool)
(declare-fun Set_union (Set<$Ref> Set<$Ref>) Set<$Ref>)
(declare-fun Set_unionone (Set<$Ref> $Ref) Set<$Ref>)
(declare-fun Set_singleton ($Ref) Set<$Ref>)
(declare-const Set_empty Set<$Ref>)
(declare-fun Set_card (Set<$Ref>) Int)
(declare-fun Set_in ($Ref Set<$Ref>) Bool)
; /dafny_axioms/sequences_declarations_dafny.smt2 [Int]
(declare-fun $Seq.length ($Seq<Int>) Int)
(declare-fun $Seq.empty<Int> () $Seq<Int>)
(declare-fun $Seq.singleton (Int) $Seq<Int>)
(declare-fun $Seq.build ($Seq<Int> Int) $Seq<Int>)
(declare-fun $Seq.index ($Seq<Int> Int) Int)
(declare-fun $Seq.append ($Seq<Int> $Seq<Int>) $Seq<Int>)
(declare-fun $Seq.update ($Seq<Int> Int Int) $Seq<Int>)
(declare-fun $Seq.contains ($Seq<Int> Int) Bool)
(declare-fun $Seq.take ($Seq<Int> Int) $Seq<Int>)
(declare-fun $Seq.drop ($Seq<Int> Int) $Seq<Int>)
(declare-fun $Seq.equal ($Seq<Int> $Seq<Int>) Bool)
(declare-fun $Seq.sameuntil ($Seq<Int> $Seq<Int> Int) Bool)
; /dafny_axioms/sequences_declarations_dafny.smt2 [Ref]
(declare-fun $Seq.length ($Seq<$Ref>) Int)
(declare-fun $Seq.empty<$Ref> () $Seq<$Ref>)
(declare-fun $Seq.singleton ($Ref) $Seq<$Ref>)
(declare-fun $Seq.build ($Seq<$Ref> $Ref) $Seq<$Ref>)
(declare-fun $Seq.index ($Seq<$Ref> Int) $Ref)
(declare-fun $Seq.append ($Seq<$Ref> $Seq<$Ref>) $Seq<$Ref>)
(declare-fun $Seq.update ($Seq<$Ref> Int $Ref) $Seq<$Ref>)
(declare-fun $Seq.contains ($Seq<$Ref> $Ref) Bool)
(declare-fun $Seq.take ($Seq<$Ref> Int) $Seq<$Ref>)
(declare-fun $Seq.drop ($Seq<$Ref> Int) $Seq<$Ref>)
(declare-fun $Seq.equal ($Seq<$Ref> $Seq<$Ref>) Bool)
(declare-fun $Seq.sameuntil ($Seq<$Ref> $Seq<$Ref> Int) Bool)
; /dafny_axioms/sequences_int_declarations_dafny.smt2
(declare-fun $Seq.range (Int Int) $Seq<Int>)
; /field_value_functions_declarations.smt2 [Ref__Integer_value: Int]
(declare-fun $FVF.domain_Ref__Integer_value ($FVF<Int>) Set<$Ref>)
(declare-fun $FVF.lookup_Ref__Integer_value ($FVF<Int> $Ref) Int)
(declare-fun $FVF.after_Ref__Integer_value ($FVF<Int> $FVF<Int>) Bool)
(declare-const $fvfTOP_Ref__Integer_value $FVF<Int>)
; /dafny_axioms/qpp_sets_declarations_dafny.smt2 [Snap]
(declare-fun Set_equal (Set<$Snap> Set<$Snap>) Bool)
(declare-fun Set_in ($Snap Set<$Snap>) Bool)
(declare-fun Set_singleton ($Snap) Set<$Snap>)
; Declaring symbols related to program functions (from program analysis)
(declare-fun count_list ($Snap Int Int $Seq<Int> Int) Int)
(declare-fun count_list%limited ($Snap Int Int $Seq<Int> Int) Int)
(declare-fun count_list%stateless (Int Int $Seq<Int> Int) Bool)
(declare-fun count_square ($Snap Int Int Int Int Int Int $Seq<$Ref> Int) Int)
(declare-fun count_square%limited ($Snap Int Int Int Int Int Int $Seq<$Ref> Int) Int)
(declare-fun count_square%stateless (Int Int Int Int Int Int $Seq<$Ref> Int) Bool)
(declare-fun sum_square ($Snap Int Int Int Int Int Int $Seq<$Ref>) Int)
(declare-fun sum_square%limited ($Snap Int Int Int Int Int Int $Seq<$Ref>) Int)
(declare-fun sum_square%stateless (Int Int Int Int Int Int $Seq<$Ref>) Bool)
(declare-fun sum_list ($Snap Int Int $Seq<Int>) Int)
(declare-fun sum_list%limited ($Snap Int Int $Seq<Int>) Int)
(declare-fun sum_list%stateless (Int Int $Seq<Int>) Bool)
(declare-fun sum_array ($Snap Int Int Int $Seq<$Ref>) Int)
(declare-fun sum_array%limited ($Snap Int Int Int $Seq<$Ref>) Int)
(declare-fun sum_array%stateless (Int Int Int $Seq<$Ref>) Bool)
(declare-fun count_array ($Snap Int Int $Seq<$Ref> Int) Int)
(declare-fun count_array%limited ($Snap Int Int $Seq<$Ref> Int) Int)
(declare-fun count_array%stateless (Int Int $Seq<$Ref> Int) Bool)
; Snapshot variable to be used during function verification
(declare-fun s@$ () $Snap)
; Declaring predicate trigger functions
; ////////// Uniqueness assumptions from domains
; ////////// Axioms
; /dafny_axioms/sequences_axioms_dafny.smt2 [Int]
(assert (forall ((s $Seq<Int>) ) (! (<= 0 ($Seq.length s))
  :pattern ( ($Seq.length s))
  )))
(assert (= ($Seq.length $Seq.empty<Int>) 0))
(assert (forall ((s $Seq<Int>) ) (! (=> (= ($Seq.length s) 0) (= s $Seq.empty<Int>))
  :pattern ( ($Seq.length s))
  )))
(assert (forall ((t Int) ) (! (= ($Seq.length ($Seq.singleton t)) 1)
  :pattern ( ($Seq.length ($Seq.singleton t)))
  )))
(assert (forall ((s $Seq<Int>) (v Int) ) (! (= ($Seq.length ($Seq.build s v)) (+ 1 ($Seq.length s)))
  :pattern ( ($Seq.length ($Seq.build s v)))
  )))
(assert (forall ((s $Seq<Int>) (i Int) (v Int) ) (! (and
  (=> (= i ($Seq.length s)) (= ($Seq.index ($Seq.build s v) i) v))
  (=> (not (= i ($Seq.length s))) (= ($Seq.index ($Seq.build s v) i) ($Seq.index s i))))
  :pattern ( ($Seq.index ($Seq.build s v) i))
  )))
(assert (forall ((s0 $Seq<Int>) (s1 $Seq<Int>) ) (!
  (implies ; The implication was not in the Dafny version
    (and
      (not (= s0 $Seq.empty<Int>))
      (not (= s1 $Seq.empty<Int>)))
    (=
      ($Seq.length ($Seq.append s0 s1))
      (+ ($Seq.length s0) ($Seq.length s1))))
  :pattern ( ($Seq.length ($Seq.append s0 s1)))
  )))
(assert (forall ((t Int) ) (! (= ($Seq.index ($Seq.singleton t) 0) t)
  :pattern ( ($Seq.index ($Seq.singleton t) 0))
  )))
(assert (forall ((s $Seq<Int>)) (! ; The axiom was not in the Dafny version
  (= ($Seq.append s $Seq.empty<Int>) s)
  :pattern (($Seq.append s $Seq.empty<Int>))
  )))
(assert (forall ((s $Seq<Int>)) (! ; The axiom was not in the Dafny version
  (= ($Seq.append $Seq.empty<Int> s) s)
  :pattern (($Seq.append $Seq.empty<Int> s))
  )))
(assert (forall ((s0 $Seq<Int>) (s1 $Seq<Int>) (n Int) ) (!
  (implies ; The implication was not in the Dafny version
    (and
      (not (= s0 $Seq.empty<Int>))
      (not (= s1 $Seq.empty<Int>)))
    (and
      (=> (< n ($Seq.length s0)) (= ($Seq.index ($Seq.append s0 s1) n) ($Seq.index s0 n)))
      (=> (<= ($Seq.length s0) n) (= ($Seq.index ($Seq.append s0 s1) n) ($Seq.index s1 (- n ($Seq.length s0)))))))
  :pattern ( ($Seq.index ($Seq.append s0 s1) n))
  )))
(assert (forall ((s $Seq<Int>) (i Int) (v Int) ) (! (=> (and
  (<= 0 i)
  (< i ($Seq.length s))) (= ($Seq.length ($Seq.update s i v)) ($Seq.length s)))
  :pattern ( ($Seq.length ($Seq.update s i v)))
  )))
(assert (forall ((s $Seq<Int>) (i Int) (v Int) (n Int) ) (! (=> (and
  (<= 0 n)
  (< n ($Seq.length s))) (and
  (=> (= i n) (= ($Seq.index ($Seq.update s i v) n) v))
  (=> (not (= i n)) (= ($Seq.index ($Seq.update s i v) n) ($Seq.index s n)))))
  :pattern ( ($Seq.index ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<Int>) (x Int) ) (!
  (and
    (=>
      ($Seq.contains s x)
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
  )))
    (=>
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains s x)))
  :pattern ( ($Seq.contains s x))
  )))
(assert (forall ((x Int) ) (! (not ($Seq.contains $Seq.empty<Int> x))
  :pattern ( ($Seq.contains $Seq.empty<Int> x))
  )))
(assert (forall ((s0 $Seq<Int>) (s1 $Seq<Int>) (x Int) ) (! (and
  (=> ($Seq.contains ($Seq.append s0 s1) x) (or
  ($Seq.contains s0 x)
  ($Seq.contains s1 x)))
  (=> (or
  ($Seq.contains s0 x)
  ($Seq.contains s1 x)) ($Seq.contains ($Seq.append s0 s1) x)))
  :pattern ( ($Seq.contains ($Seq.append s0 s1) x))
  )))
(assert (forall ((s $Seq<Int>) (v Int) (x Int) ) (! (and
  (=> ($Seq.contains ($Seq.build s v) x) (or
  (= v x)
  ($Seq.contains s x)))
  (=> (or
  (= v x)
  ($Seq.contains s x)) ($Seq.contains ($Seq.build s v) x)))
  :pattern ( ($Seq.contains ($Seq.build s v) x))
  )))
(assert (forall ((s $Seq<Int>) (n Int) (x Int) ) (!
  (and
    (=>
      ($Seq.contains ($Seq.take s n) x)
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i n)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
  )))
    (=>
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i n)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains ($Seq.take s n) x)))
  :pattern ( ($Seq.contains ($Seq.take s n) x))
  )))
(assert (forall ((s $Seq<Int>) (n Int) (x Int) ) (!
  (and
    (=>
      ($Seq.contains ($Seq.drop s n) x)
      (exists ((i Int) ) (!
        (and
  (<= 0 n)
  (<= n i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
  )))
    (=>
      (exists ((i Int) ) (!
        (and
  (<= 0 n)
  (<= n i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains ($Seq.drop s n) x)))
  :pattern ( ($Seq.contains ($Seq.drop s n) x))
  )))
(assert (forall ((s0 $Seq<Int>) (s1 $Seq<Int>) ) (! (and
  (=> ($Seq.equal s0 s1) (and
  (= ($Seq.length s0) ($Seq.length s1))
  (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j ($Seq.length s0))) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  ))))
  (=> (and
  (= ($Seq.length s0) ($Seq.length s1))
  (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j ($Seq.length s0))) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  ))) ($Seq.equal s0 s1)))
  :pattern ( ($Seq.equal s0 s1))
  )))
(assert (forall ((a $Seq<Int>) (b $Seq<Int>) ) (! (=> ($Seq.equal a b) (= a b))
  :pattern ( ($Seq.equal a b))
  )))
(assert (forall ((s0 $Seq<Int>) (s1 $Seq<Int>) (n Int) ) (! (and
  (=> ($Seq.sameuntil s0 s1 n) (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  )))
  (=> (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  )) ($Seq.sameuntil s0 s1 n)))
  :pattern ( ($Seq.sameuntil s0 s1 n))
  )))
(assert (forall ((s $Seq<Int>) (n Int) ) (! (=> (<= 0 n) (and
  (=> (<= n ($Seq.length s)) (= ($Seq.length ($Seq.take s n)) n))
  (=> (< ($Seq.length s) n) (= ($Seq.length ($Seq.take s n)) ($Seq.length s)))))
  :pattern ( ($Seq.length ($Seq.take s n)))
  )))
(assert (forall ((s $Seq<Int>) (n Int) (j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)
  (< j ($Seq.length s))) (= ($Seq.index ($Seq.take s n) j) ($Seq.index s j)))
  :pattern ( ($Seq.index ($Seq.take s n) j))
  :pattern (($Seq.index s j) ($Seq.take s n)) ; [XXX] Added 29-10-2015
  )))
(assert (forall ((s $Seq<Int>) (n Int) ) (! (=> (<= 0 n) (and
  (=> (<= n ($Seq.length s)) (= ($Seq.length ($Seq.drop s n)) (- ($Seq.length s) n)))
  (=> (< ($Seq.length s) n) (= ($Seq.length ($Seq.drop s n)) 0))))
  :pattern ( ($Seq.length ($Seq.drop s n)))
  )))
(assert (forall ((s $Seq<Int>) (n Int) (j Int) ) (! (=> (and
  (<= 0 n)
  (<= 0 j)
  (< j (- ($Seq.length s) n))) (= ($Seq.index ($Seq.drop s n) j) ($Seq.index s (+ j n))))
  :pattern ( ($Seq.index ($Seq.drop s n) j))
  )))
(assert (forall ((s $Seq<Int>) (n Int) (k Int) ) (! ; [XXX] Added 29-10-2015
  (=>
    (and
      (<= 0 n)
      (<= n k)
      (< k ($Seq.length s)))
    (=
      ($Seq.index ($Seq.drop s n) (- k n))
      ($Seq.index s k)))
  :pattern (($Seq.index s k) ($Seq.drop s n))
  )))
(assert (forall ((s $Seq<Int>) (i Int) (v Int) (n Int) ) (! (=> (and
  (<= 0 i)
  (< i n)
  (<= n ($Seq.length s))) (= ($Seq.take ($Seq.update s i v) n) ($Seq.update ($Seq.take s n) i v)))
  :pattern ( ($Seq.take ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<Int>) (i Int) (v Int) (n Int) ) (! (=> (and
  (<= n i)
  (< i ($Seq.length s))) (= ($Seq.take ($Seq.update s i v) n) ($Seq.take s n)))
  :pattern ( ($Seq.take ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<Int>) (i Int) (v Int) (n Int) ) (! (=> (and
  (<= 0 n)
  (<= n i)
  (< i ($Seq.length s))) (= ($Seq.drop ($Seq.update s i v) n) ($Seq.update ($Seq.drop s n) (- i n) v)))
  :pattern ( ($Seq.drop ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<Int>) (i Int) (v Int) (n Int) ) (! (=> (and
  (<= 0 i)
  (< i n)
  (< n ($Seq.length s))) (= ($Seq.drop ($Seq.update s i v) n) ($Seq.drop s n)))
  :pattern ( ($Seq.drop ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<Int>) (v Int) (n Int) ) (! (=> (and
  (<= 0 n)
  (<= n ($Seq.length s))) (= ($Seq.drop ($Seq.build s v) n) ($Seq.build ($Seq.drop s n) v)))
  :pattern ( ($Seq.drop ($Seq.build s v) n))
  )))
(assert (forall ((x Int) (y Int)) (!
  (iff
    ($Seq.contains ($Seq.singleton x) y)
    (= x y))
  :pattern (($Seq.contains ($Seq.singleton x) y))
  )))
; /dafny_axioms/sequences_axioms_dafny.smt2 [Ref]
(assert (forall ((s $Seq<$Ref>) ) (! (<= 0 ($Seq.length s))
  :pattern ( ($Seq.length s))
  )))
(assert (= ($Seq.length $Seq.empty<$Ref>) 0))
(assert (forall ((s $Seq<$Ref>) ) (! (=> (= ($Seq.length s) 0) (= s $Seq.empty<$Ref>))
  :pattern ( ($Seq.length s))
  )))
(assert (forall ((t $Ref) ) (! (= ($Seq.length ($Seq.singleton t)) 1)
  :pattern ( ($Seq.length ($Seq.singleton t)))
  )))
(assert (forall ((s $Seq<$Ref>) (v $Ref) ) (! (= ($Seq.length ($Seq.build s v)) (+ 1 ($Seq.length s)))
  :pattern ( ($Seq.length ($Seq.build s v)))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) ) (! (and
  (=> (= i ($Seq.length s)) (= ($Seq.index ($Seq.build s v) i) v))
  (=> (not (= i ($Seq.length s))) (= ($Seq.index ($Seq.build s v) i) ($Seq.index s i))))
  :pattern ( ($Seq.index ($Seq.build s v) i))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) ) (!
  (implies ; The implication was not in the Dafny version
    (and
      (not (= s0 $Seq.empty<$Ref>))
      (not (= s1 $Seq.empty<$Ref>)))
    (=
      ($Seq.length ($Seq.append s0 s1))
      (+ ($Seq.length s0) ($Seq.length s1))))
  :pattern ( ($Seq.length ($Seq.append s0 s1)))
  )))
(assert (forall ((t $Ref) ) (! (= ($Seq.index ($Seq.singleton t) 0) t)
  :pattern ( ($Seq.index ($Seq.singleton t) 0))
  )))
(assert (forall ((s $Seq<$Ref>)) (! ; The axiom was not in the Dafny version
  (= ($Seq.append s $Seq.empty<$Ref>) s)
  :pattern (($Seq.append s $Seq.empty<$Ref>))
  )))
(assert (forall ((s $Seq<$Ref>)) (! ; The axiom was not in the Dafny version
  (= ($Seq.append $Seq.empty<$Ref> s) s)
  :pattern (($Seq.append $Seq.empty<$Ref> s))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) (n Int) ) (!
  (implies ; The implication was not in the Dafny version
    (and
      (not (= s0 $Seq.empty<$Ref>))
      (not (= s1 $Seq.empty<$Ref>)))
    (and
      (=> (< n ($Seq.length s0)) (= ($Seq.index ($Seq.append s0 s1) n) ($Seq.index s0 n)))
      (=> (<= ($Seq.length s0) n) (= ($Seq.index ($Seq.append s0 s1) n) ($Seq.index s1 (- n ($Seq.length s0)))))))
  :pattern ( ($Seq.index ($Seq.append s0 s1) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) ) (! (=> (and
  (<= 0 i)
  (< i ($Seq.length s))) (= ($Seq.length ($Seq.update s i v)) ($Seq.length s)))
  :pattern ( ($Seq.length ($Seq.update s i v)))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 n)
  (< n ($Seq.length s))) (and
  (=> (= i n) (= ($Seq.index ($Seq.update s i v) n) v))
  (=> (not (= i n)) (= ($Seq.index ($Seq.update s i v) n) ($Seq.index s n)))))
  :pattern ( ($Seq.index ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (x $Ref) ) (!
  (and
    (=>
      ($Seq.contains s x)
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
  )))
    (=>
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains s x)))
  :pattern ( ($Seq.contains s x))
  )))
(assert (forall ((x $Ref) ) (! (not ($Seq.contains $Seq.empty<$Ref> x))
  :pattern ( ($Seq.contains $Seq.empty<$Ref> x))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) (x $Ref) ) (! (and
  (=> ($Seq.contains ($Seq.append s0 s1) x) (or
  ($Seq.contains s0 x)
  ($Seq.contains s1 x)))
  (=> (or
  ($Seq.contains s0 x)
  ($Seq.contains s1 x)) ($Seq.contains ($Seq.append s0 s1) x)))
  :pattern ( ($Seq.contains ($Seq.append s0 s1) x))
  )))
(assert (forall ((s $Seq<$Ref>) (v $Ref) (x $Ref) ) (! (and
  (=> ($Seq.contains ($Seq.build s v) x) (or
  (= v x)
  ($Seq.contains s x)))
  (=> (or
  (= v x)
  ($Seq.contains s x)) ($Seq.contains ($Seq.build s v) x)))
  :pattern ( ($Seq.contains ($Seq.build s v) x))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (x $Ref) ) (!
  (and
    (=>
      ($Seq.contains ($Seq.take s n) x)
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i n)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
  )))
    (=>
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i n)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains ($Seq.take s n) x)))
  :pattern ( ($Seq.contains ($Seq.take s n) x))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (x $Ref) ) (!
  (and
    (=>
      ($Seq.contains ($Seq.drop s n) x)
      (exists ((i Int) ) (!
        (and
  (<= 0 n)
  (<= n i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
  )))
    (=>
      (exists ((i Int) ) (!
        (and
  (<= 0 n)
  (<= n i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains ($Seq.drop s n) x)))
  :pattern ( ($Seq.contains ($Seq.drop s n) x))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) ) (! (and
  (=> ($Seq.equal s0 s1) (and
  (= ($Seq.length s0) ($Seq.length s1))
  (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j ($Seq.length s0))) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  ))))
  (=> (and
  (= ($Seq.length s0) ($Seq.length s1))
  (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j ($Seq.length s0))) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  ))) ($Seq.equal s0 s1)))
  :pattern ( ($Seq.equal s0 s1))
  )))
(assert (forall ((a $Seq<$Ref>) (b $Seq<$Ref>) ) (! (=> ($Seq.equal a b) (= a b))
  :pattern ( ($Seq.equal a b))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) (n Int) ) (! (and
  (=> ($Seq.sameuntil s0 s1 n) (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  )))
  (=> (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  )) ($Seq.sameuntil s0 s1 n)))
  :pattern ( ($Seq.sameuntil s0 s1 n))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) ) (! (=> (<= 0 n) (and
  (=> (<= n ($Seq.length s)) (= ($Seq.length ($Seq.take s n)) n))
  (=> (< ($Seq.length s) n) (= ($Seq.length ($Seq.take s n)) ($Seq.length s)))))
  :pattern ( ($Seq.length ($Seq.take s n)))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)
  (< j ($Seq.length s))) (= ($Seq.index ($Seq.take s n) j) ($Seq.index s j)))
  :pattern ( ($Seq.index ($Seq.take s n) j))
  :pattern (($Seq.index s j) ($Seq.take s n)) ; [XXX] Added 29-10-2015
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) ) (! (=> (<= 0 n) (and
  (=> (<= n ($Seq.length s)) (= ($Seq.length ($Seq.drop s n)) (- ($Seq.length s) n)))
  (=> (< ($Seq.length s) n) (= ($Seq.length ($Seq.drop s n)) 0))))
  :pattern ( ($Seq.length ($Seq.drop s n)))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (j Int) ) (! (=> (and
  (<= 0 n)
  (<= 0 j)
  (< j (- ($Seq.length s) n))) (= ($Seq.index ($Seq.drop s n) j) ($Seq.index s (+ j n))))
  :pattern ( ($Seq.index ($Seq.drop s n) j))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (k Int) ) (! ; [XXX] Added 29-10-2015
  (=>
    (and
      (<= 0 n)
      (<= n k)
      (< k ($Seq.length s)))
    (=
      ($Seq.index ($Seq.drop s n) (- k n))
      ($Seq.index s k)))
  :pattern (($Seq.index s k) ($Seq.drop s n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 i)
  (< i n)
  (<= n ($Seq.length s))) (= ($Seq.take ($Seq.update s i v) n) ($Seq.update ($Seq.take s n) i v)))
  :pattern ( ($Seq.take ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= n i)
  (< i ($Seq.length s))) (= ($Seq.take ($Seq.update s i v) n) ($Seq.take s n)))
  :pattern ( ($Seq.take ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 n)
  (<= n i)
  (< i ($Seq.length s))) (= ($Seq.drop ($Seq.update s i v) n) ($Seq.update ($Seq.drop s n) (- i n) v)))
  :pattern ( ($Seq.drop ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 i)
  (< i n)
  (< n ($Seq.length s))) (= ($Seq.drop ($Seq.update s i v) n) ($Seq.drop s n)))
  :pattern ( ($Seq.drop ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 n)
  (<= n ($Seq.length s))) (= ($Seq.drop ($Seq.build s v) n) ($Seq.build ($Seq.drop s n) v)))
  :pattern ( ($Seq.drop ($Seq.build s v) n))
  )))
(assert (forall ((x $Ref) (y $Ref)) (!
  (iff
    ($Seq.contains ($Seq.singleton x) y)
    (= x y))
  :pattern (($Seq.contains ($Seq.singleton x) y))
  )))
; /dafny_axioms/sequences_int_axioms_dafny.smt2
(assert (forall ((min Int) (max Int) ) (! (and
  (=> (< min max) (= ($Seq.length ($Seq.range min max)) (- max min)))
  (=> (<= max min) (= ($Seq.length ($Seq.range min max)) 0)))
   :pattern ( ($Seq.length ($Seq.range min max)))
  )))
(assert (forall ((min Int) (max Int) (j Int) ) (! (=> (and
  (<= 0 j)
  (< j (- max min))) (= ($Seq.index ($Seq.range min max) j) (+ min j)))
   :pattern ( ($Seq.index ($Seq.range min max) j))
  )))
(assert (forall ((min Int) (max Int) (v Int) ) (! (and
  (=> ($Seq.contains ($Seq.range min max) v) (and
  (<= min v)
  (< v max)))
  (=> (and
  (<= min v)
  (< v max)) ($Seq.contains ($Seq.range min max) v)))
   :pattern ( ($Seq.contains ($Seq.range min max) v))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (and
    (=
      (+
        (+ (Set_card (Set_difference s1 s2)) (Set_card (Set_difference s2 s1)))
        (Set_card (Set_intersection s1 s2)))
      (Set_card (Set_union s1 s2)))
    (=
      (Set_card (Set_difference s1 s2))
      (- (Set_card s1) (Set_card (Set_intersection s1 s2)))))
  :pattern ((Set_card (Set_difference s1 s2)))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (=
    (Set_disjoint s1 s2)
    (and
      (forall ((e Int)) (!
        (or (not (Set_in e s1)) (not (Set_in e s2)))
        :pattern ((Set_in e s1))
        ))
      (forall ((e Int)) (!
        (or (not (Set_in e s1)) (not (Set_in e s2)))
        :pattern ((Set_in e s2))
        ))))
  :pattern ((Set_disjoint s1 s2))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (implies (Set_equal s1 s2) (= s1 s2))
  :pattern ((Set_equal s1 s2))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (=
    (Set_equal s1 s2)
    (and
      (forall ((e Int)) (!
        (= (Set_in e s1) (Set_in e s2))
        :pattern ((Set_in e s1))
        ))
      (forall ((e Int)) (!
        (= (Set_in e s1) (Set_in e s2))
        :pattern ((Set_in e s2))
        ))))
  :pattern ((Set_equal s1 s2))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (=
    (Set_subset s1 s2)
    (and
      (forall ((e Int)) (!
        (implies (Set_in e s1) (Set_in e s2))
        :pattern ((Set_in e s1))
        ))
      (forall ((e Int)) (!
        (implies (Set_in e s1) (Set_in e s2))
        :pattern ((Set_in e s2))
        ))))
  :pattern ((Set_subset s1 s2))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (implies (Set_in e s2) (not (Set_in e (Set_difference s1 s2))))
  :pattern ((Set_difference s1 s2) (Set_in e s2))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (= (Set_in e (Set_difference s1 s2)) (and (Set_in e s1) (not (Set_in e s2))))
  :pattern ((Set_in e (Set_difference s1 s2)))
  )))
(assert (and
  (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
    (=
      (+ (Set_card (Set_union s1 s2)) (Set_card (Set_intersection s1 s2)))
      (+ (Set_card s1) (Set_card s2)))
    :pattern ((Set_card (Set_union s1 s2)))
    ))
  (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
    (=
      (+ (Set_card (Set_union s1 s2)) (Set_card (Set_intersection s1 s2)))
      (+ (Set_card s1) (Set_card s2)))
    :pattern ((Set_card (Set_intersection s1 s2)))
    ))))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (= (Set_intersection (Set_intersection s1 s2) s2) (Set_intersection s1 s2))
  :pattern ((Set_intersection (Set_intersection s1 s2) s2))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (= (Set_intersection s1 (Set_intersection s1 s2)) (Set_intersection s1 s2))
  :pattern ((Set_intersection s1 (Set_intersection s1 s2)))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (= (Set_union (Set_union s1 s2) s2) (Set_union s1 s2))
  :pattern ((Set_union (Set_union s1 s2) s2))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>)) (!
  (= (Set_union s1 (Set_union s1 s2)) (Set_union s1 s2))
  :pattern ((Set_union s1 (Set_union s1 s2)))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (= (Set_in e (Set_intersection s1 s2)) (and (Set_in e s1) (Set_in e s2)))
  :pattern ((Set_in e (Set_intersection s1 s2)))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (implies (Set_in e s2) (Set_in e (Set_union s1 s2)))
  :pattern ((Set_in e s2) (Set_union s1 s2))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (implies (Set_in e s1) (Set_in e (Set_union s1 s2)))
  :pattern ((Set_in e s1) (Set_union s1 s2))
  )))
(assert (forall ((s1 Set<Int>) (s2 Set<Int>) (e Int)) (!
  (= (Set_in e (Set_union s1 s2)) (or (Set_in e s1) (Set_in e s2)))
  :pattern ((Set_in e (Set_union s1 s2)))
  )))
(assert (forall ((s Set<Int>) (e Int)) (!
  (implies
    (not (Set_in e s))
    (= (Set_card (Set_unionone s e)) (+ (Set_card s) 1)))
  :pattern ((Set_card (Set_unionone s e)))
  )))
(assert (forall ((s Set<Int>) (e Int)) (!
  (implies (Set_in e s) (= (Set_card (Set_unionone s e)) (Set_card s)))
  :pattern ((Set_card (Set_unionone s e)))
  )))
(assert (forall ((s Set<Int>) (e1 Int) (e2 Int)) (!
  (implies (Set_in e1 s) (Set_in e1 (Set_unionone s e2)))
  :pattern ((Set_in e1 s) (Set_unionone s e2))
  )))
(assert (forall ((s Set<Int>) (e1 Int) (e2 Int)) (!
  (= (Set_in e1 (Set_unionone s e2)) (or (= e1 e2) (Set_in e1 s)))
  :pattern ((Set_in e1 (Set_unionone s e2)))
  )))
(assert (forall ((s Set<Int>) (e Int)) (!
  (Set_in e (Set_unionone s e))
  :pattern ((Set_unionone s e))
  )))
(assert (forall ((e Int)) (!
  (= (Set_card (Set_singleton e)) 1)
  :pattern ((Set_card (Set_singleton e)))
  )))
(assert (forall ((e1 Int) (e2 Int)) (!
  (= (Set_in e1 (Set_singleton e2)) (= e1 e2))
  :pattern ((Set_in e1 (Set_singleton e2)))
  )))
(assert (forall ((e Int)) (!
  (Set_in e (Set_singleton e))
  :pattern ((Set_singleton e))
  )))
(assert (forall ((s Set<Int>)) (!
  (and
    (= (= (Set_card s) 0) (= s (as Set_empty  Set<Int>)))
    (implies (not (= (Set_card s) 0)) (exists ((e Int)) (! (Set_in e s)  ))))
  :pattern ((Set_card s))
  )))
(assert (forall ((e Int)) (!
  (not (Set_in e (as Set_empty  Set<Int>)))
  :pattern ((Set_in e (as Set_empty  Set<Int>)))
  )))
(assert (forall ((s Set<Int>)) (!
  (<= 0 (Set_card s))
  :pattern ((Set_card s))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (and
    (=
      (+
        (+ (Set_card (Set_difference s1 s2)) (Set_card (Set_difference s2 s1)))
        (Set_card (Set_intersection s1 s2)))
      (Set_card (Set_union s1 s2)))
    (=
      (Set_card (Set_difference s1 s2))
      (- (Set_card s1) (Set_card (Set_intersection s1 s2)))))
  :pattern ((Set_card (Set_difference s1 s2)))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (=
    (Set_disjoint s1 s2)
    (and
      (forall ((e $Ref)) (!
        (or (not (Set_in e s1)) (not (Set_in e s2)))
        :pattern ((Set_in e s1))
        ))
      (forall ((e $Ref)) (!
        (or (not (Set_in e s1)) (not (Set_in e s2)))
        :pattern ((Set_in e s2))
        ))))
  :pattern ((Set_disjoint s1 s2))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (implies (Set_equal s1 s2) (= s1 s2))
  :pattern ((Set_equal s1 s2))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (=
    (Set_equal s1 s2)
    (and
      (forall ((e $Ref)) (!
        (= (Set_in e s1) (Set_in e s2))
        :pattern ((Set_in e s1))
        ))
      (forall ((e $Ref)) (!
        (= (Set_in e s1) (Set_in e s2))
        :pattern ((Set_in e s2))
        ))))
  :pattern ((Set_equal s1 s2))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (=
    (Set_subset s1 s2)
    (and
      (forall ((e $Ref)) (!
        (implies (Set_in e s1) (Set_in e s2))
        :pattern ((Set_in e s1))
        ))
      (forall ((e $Ref)) (!
        (implies (Set_in e s1) (Set_in e s2))
        :pattern ((Set_in e s2))
        ))))
  :pattern ((Set_subset s1 s2))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (implies (Set_in e s2) (not (Set_in e (Set_difference s1 s2))))
  :pattern ((Set_difference s1 s2) (Set_in e s2))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (= (Set_in e (Set_difference s1 s2)) (and (Set_in e s1) (not (Set_in e s2))))
  :pattern ((Set_in e (Set_difference s1 s2)))
  )))
(assert (and
  (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
    (=
      (+ (Set_card (Set_union s1 s2)) (Set_card (Set_intersection s1 s2)))
      (+ (Set_card s1) (Set_card s2)))
    :pattern ((Set_card (Set_union s1 s2)))
    ))
  (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
    (=
      (+ (Set_card (Set_union s1 s2)) (Set_card (Set_intersection s1 s2)))
      (+ (Set_card s1) (Set_card s2)))
    :pattern ((Set_card (Set_intersection s1 s2)))
    ))))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (= (Set_intersection (Set_intersection s1 s2) s2) (Set_intersection s1 s2))
  :pattern ((Set_intersection (Set_intersection s1 s2) s2))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (= (Set_intersection s1 (Set_intersection s1 s2)) (Set_intersection s1 s2))
  :pattern ((Set_intersection s1 (Set_intersection s1 s2)))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (= (Set_union (Set_union s1 s2) s2) (Set_union s1 s2))
  :pattern ((Set_union (Set_union s1 s2) s2))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>)) (!
  (= (Set_union s1 (Set_union s1 s2)) (Set_union s1 s2))
  :pattern ((Set_union s1 (Set_union s1 s2)))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (= (Set_in e (Set_intersection s1 s2)) (and (Set_in e s1) (Set_in e s2)))
  :pattern ((Set_in e (Set_intersection s1 s2)))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (implies (Set_in e s2) (Set_in e (Set_union s1 s2)))
  :pattern ((Set_in e s2) (Set_union s1 s2))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (implies (Set_in e s1) (Set_in e (Set_union s1 s2)))
  :pattern ((Set_in e s1) (Set_union s1 s2))
  )))
(assert (forall ((s1 Set<$Ref>) (s2 Set<$Ref>) (e $Ref)) (!
  (= (Set_in e (Set_union s1 s2)) (or (Set_in e s1) (Set_in e s2)))
  :pattern ((Set_in e (Set_union s1 s2)))
  )))
(assert (forall ((s Set<$Ref>) (e $Ref)) (!
  (implies
    (not (Set_in e s))
    (= (Set_card (Set_unionone s e)) (+ (Set_card s) 1)))
  :pattern ((Set_card (Set_unionone s e)))
  )))
(assert (forall ((s Set<$Ref>) (e $Ref)) (!
  (implies (Set_in e s) (= (Set_card (Set_unionone s e)) (Set_card s)))
  :pattern ((Set_card (Set_unionone s e)))
  )))
(assert (forall ((s Set<$Ref>) (e1 $Ref) (e2 $Ref)) (!
  (implies (Set_in e1 s) (Set_in e1 (Set_unionone s e2)))
  :pattern ((Set_in e1 s) (Set_unionone s e2))
  )))
(assert (forall ((s Set<$Ref>) (e1 $Ref) (e2 $Ref)) (!
  (= (Set_in e1 (Set_unionone s e2)) (or (= e1 e2) (Set_in e1 s)))
  :pattern ((Set_in e1 (Set_unionone s e2)))
  )))
(assert (forall ((s Set<$Ref>) (e $Ref)) (!
  (Set_in e (Set_unionone s e))
  :pattern ((Set_unionone s e))
  )))
(assert (forall ((e $Ref)) (!
  (= (Set_card (Set_singleton e)) 1)
  :pattern ((Set_card (Set_singleton e)))
  )))
(assert (forall ((e1 $Ref) (e2 $Ref)) (!
  (= (Set_in e1 (Set_singleton e2)) (= e1 e2))
  :pattern ((Set_in e1 (Set_singleton e2)))
  )))
(assert (forall ((e $Ref)) (!
  (Set_in e (Set_singleton e))
  :pattern ((Set_singleton e))
  )))
(assert (forall ((s Set<$Ref>)) (!
  (and
    (= (= (Set_card s) 0) (= s (as Set_empty  Set<$Ref>)))
    (implies (not (= (Set_card s) 0)) (exists ((e $Ref)) (! (Set_in e s)  ))))
  :pattern ((Set_card s))
  )))
(assert (forall ((e $Ref)) (!
  (not (Set_in e (as Set_empty  Set<$Ref>)))
  :pattern ((Set_in e (as Set_empty  Set<$Ref>)))
  )))
(assert (forall ((s Set<$Ref>)) (!
  (<= 0 (Set_card s))
  :pattern ((Set_card s))
  )))
; /field_value_functions_axioms.smt2 [Ref__Integer_value: Int]
(assert (forall ((vs $FVF<Int>) (ws $FVF<Int>)) (!
    (implies
      (and
        (Set_equal ($FVF.domain_Ref__Integer_value vs) ($FVF.domain_Ref__Integer_value ws))
        (forall ((x $Ref)) (!
          (implies
            (Set_in x ($FVF.domain_Ref__Integer_value vs))
            (= ($FVF.lookup_Ref__Integer_value vs x) ($FVF.lookup_Ref__Integer_value ws x)))
          :pattern (($FVF.lookup_Ref__Integer_value vs x) ($FVF.lookup_Ref__Integer_value ws x))
          :qid |qp.$FVF<Int>-eq-inner|
          )))
      (= vs ws))
    :pattern (($SortWrappers.$FVF<Int>To$Snap vs)
              ($SortWrappers.$FVF<Int>To$Snap ws)
              )
    :qid |qp.$FVF<Int>-eq-outer|
    )))
; End preamble
; ------------------------------------------------------------
; State saturation: after preamble
;(set-option :timeout 100)
(set-option :rlimit 40807)

(check-sat)

; unknown
; ------------------------------------------------------------
; Begin function- and predicate-related preamble
; Declaring symbols related to program functions (from verification)
(declare-fun sm@52@00 ($Snap Int Int Int Int Int Int $Seq<$Ref> Int) $FVF<Int>)
(declare-fun sm@44@00 ($Snap Int Int Int Int Int Int $Seq<$Ref> Int) $FVF<Int>)
(declare-fun inv@50@00 ($Snap Int Int Int Int Int Int $Seq<$Ref> Int $Ref) Int)
(declare-fun $k@49@00 () $Perm)
(declare-fun inv@41@00 ($Snap Int Int Int Int Int Int $Seq<$Ref> Int $Ref) Int)
(declare-fun $k@40@00 () $Perm)
(declare-fun sm@68@00 ($Snap Int Int Int Int Int Int $Seq<$Ref>) $FVF<Int>)
(declare-fun sm@60@00 ($Snap Int Int Int Int Int Int $Seq<$Ref>) $FVF<Int>)
(declare-fun inv@66@00 ($Snap Int Int Int Int Int Int $Seq<$Ref> $Ref) Int)
(declare-fun $k@65@00 () $Perm)
(declare-fun inv@58@00 ($Snap Int Int Int Int Int Int $Seq<$Ref> $Ref) Int)
(declare-fun $k@57@00 () $Perm)
(declare-fun sm@77@00 ($Snap Int Int Int $Seq<$Ref>) $FVF<Int>)
(declare-fun sm@72@00 ($Snap Int Int Int $Seq<$Ref>) $FVF<Int>)
(declare-fun inv@75@00 ($Snap Int Int Int $Seq<$Ref> $Ref) Int)
(declare-fun $k@74@00 () $Perm)
(declare-fun inv@71@00 ($Snap Int Int Int $Seq<$Ref> $Ref) Int)
(declare-fun $k@70@00 () $Perm)
(declare-fun sm@86@00 ($Snap Int Int $Seq<$Ref> Int) $FVF<Int>)
(declare-fun sm@81@00 ($Snap Int Int $Seq<$Ref> Int) $FVF<Int>)
(declare-fun inv@84@00 ($Snap Int Int $Seq<$Ref> Int $Ref) Int)
(declare-fun $k@83@00 () $Perm)
(declare-fun inv@80@00 ($Snap Int Int $Seq<$Ref> Int $Ref) Int)
(declare-fun $k@79@00 () $Perm)
(assert (forall ((s@$ $Snap) (i@0@00 Int) (hi@1@00 Int) (ar@2@00 $Seq<Int>) (v@3@00 Int)) (!
  (=
    (count_list%limited s@$ i@0@00 hi@1@00 ar@2@00 v@3@00)
    (count_list s@$ i@0@00 hi@1@00 ar@2@00 v@3@00))
  :pattern ((count_list s@$ i@0@00 hi@1@00 ar@2@00 v@3@00))
  )))
(assert (forall ((s@$ $Snap) (i@0@00 Int) (hi@1@00 Int) (ar@2@00 $Seq<Int>) (v@3@00 Int)) (!
  (count_list%stateless i@0@00 hi@1@00 ar@2@00 v@3@00)
  :pattern ((count_list%limited s@$ i@0@00 hi@1@00 ar@2@00 v@3@00))
  )))
(assert (forall ((s@$ $Snap) (i@0@00 Int) (hi@1@00 Int) (ar@2@00 $Seq<Int>) (v@3@00 Int)) (!
  (let ((result@4@00 (count_list%limited s@$ i@0@00 hi@1@00 ar@2@00 v@3@00))) (implies
    (and
      (and (<= 0 i@0@00) (<= i@0@00 hi@1@00))
      (<= hi@1@00 ($Seq.length ar@2@00)))
    (=
      (count_list s@$ i@0@00 hi@1@00 ar@2@00 v@3@00)
      (ite
        (< i@0@00 hi@1@00)
        (+
          (ite (= ($Seq.index ar@2@00 i@0@00) v@3@00) 1 0)
          (count_list%limited ($Snap.combine
            $Snap.unit
            ($Snap.combine $Snap.unit $Snap.unit)) (+ i@0@00 1) hi@1@00 ar@2@00 v@3@00))
        0))))
  :pattern ((count_list s@$ i@0@00 hi@1@00 ar@2@00 v@3@00))
  )))
(assert (forall ((s@$ $Snap) (i@5@00 Int) (lo@6@00 Int) (hi@7@00 Int) (step@8@00 Int) (min@9@00 Int) (max@10@00 Int) (ar@11@00 $Seq<$Ref>) (v@12@00 Int)) (!
  (=
    (count_square%limited s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00)
    (count_square s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00))
  :pattern ((count_square s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00))
  )))
(assert (forall ((s@$ $Snap) (i@5@00 Int) (lo@6@00 Int) (hi@7@00 Int) (step@8@00 Int) (min@9@00 Int) (max@10@00 Int) (ar@11@00 $Seq<$Ref>) (v@12@00 Int)) (!
  (count_square%stateless i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00)
  :pattern ((count_square%limited s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00))
  )))
(assert (forall ((s@$ $Snap) (i@5@00 Int) (lo@6@00 Int) (hi@7@00 Int) (step@8@00 Int) (min@9@00 Int) (max@10@00 Int) (ar@11@00 $Seq<$Ref>) (v@12@00 Int)) (!
  (let ((result@13@00 (count_square%limited s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00))) (and
    (implies
      (and
        (and
          (<= 0 lo@6@00)
          (and (<= lo@6@00 hi@7@00) (and (<= hi@7@00 step@8@00) (> step@8@00 0))))
        (and (<= 0 min@9@00) (and (<= min@9@00 i@5@00) (<= i@5@00 max@10@00)))
        (<= max@10@00 ($Seq.length ar@11@00)))
      (=
        (count_square s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00)
        (ite
          (< i@5@00 max@10@00)
          (+
            (ite
              (and
                (<= lo@6@00 (mod i@5@00 step@8@00))
                (and
                  (< (mod i@5@00 step@8@00) hi@7@00)
                  (=
                    ($FVF.lookup_Ref__Integer_value (sm@44@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00) ($Seq.index
                      ar@11@00
                      i@5@00))
                    v@12@00)))
              1
              0)
            (count_square%limited ($Snap.combine
              $Snap.unit
              ($Snap.combine
                $Snap.unit
                ($Snap.combine
                  $Snap.unit
                  ($Snap.combine
                    $Snap.unit
                    ($Snap.combine
                      $Snap.unit
                      ($Snap.combine
                        $Snap.unit
                        ($Snap.combine
                          $Snap.unit
                          ($Snap.combine
                            $Snap.unit
                            ($SortWrappers.$FVF<Int>To$Snap (sm@52@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00)))))))))) (+
              i@5@00
              1) lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00))
          0)))
    ($Perm.isReadVar $k@49@00 $Perm.Write)
    ($Perm.isReadVar $k@40@00 $Perm.Write)
    (forall ((r $Ref)) (!
      (iff
        (Set_in r ($FVF.domain_Ref__Integer_value (sm@52@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00)))
        (and
          (and
            (<=
              min@9@00
              (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
            (implies
              (<=
                min@9@00
                (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
              (and
                (<
                  (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                  max@10@00)
                (implies
                  (<
                    (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                    max@10@00)
                  (and
                    (<=
                      lo@6@00
                      (mod
                        (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                        step@8@00))
                    (implies
                      (<=
                        lo@6@00
                        (mod
                          (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                          step@8@00))
                      (<
                        (mod
                          (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                          step@8@00)
                        hi@7@00)))))))
          (< $Perm.No $k@49@00)))
      :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (sm@52@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00))))
      :qid |qp.fvfDomDef3|))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            (and
              (and
                (<=
                  min@9@00
                  (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
                (implies
                  (<=
                    min@9@00
                    (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
                  (and
                    (<
                      (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                      max@10@00)
                    (implies
                      (<
                        (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                        max@10@00)
                      (and
                        (<=
                          lo@6@00
                          (mod
                            (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                            step@8@00))
                        (implies
                          (<=
                            lo@6@00
                            (mod
                              (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                              step@8@00))
                          (<
                            (mod
                              (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                              step@8@00)
                            hi@7@00)))))))
              (< $Perm.No $k@49@00))
            (ite
              (and
                (<=
                  min@9@00
                  (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
                (implies
                  (<=
                    min@9@00
                    (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
                  (and
                    (<
                      (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                      max@10@00)
                    (implies
                      (<
                        (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                        max@10@00)
                      (and
                        (<=
                          lo@6@00
                          (mod
                            (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                            step@8@00))
                        (implies
                          (<=
                            lo@6@00
                            (mod
                              (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                              step@8@00))
                          (<
                            (mod
                              (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                              step@8@00)
                            hi@7@00)))))))
              (< $Perm.No $k@40@00)
              false))
          (=
            ($FVF.lookup_Ref__Integer_value (sm@52@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (sm@52@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00) r))
        :qid |qp.fvfValDef2|))
      (forall ((r $Ref)) (!
        (implies
          (and
            (and
              (and
                (<=
                  min@9@00
                  (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
                (implies
                  (<=
                    min@9@00
                    (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
                  (and
                    (<
                      (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                      max@10@00)
                    (implies
                      (<
                        (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                        max@10@00)
                      (and
                        (<=
                          lo@6@00
                          (mod
                            (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                            step@8@00))
                        (implies
                          (<=
                            lo@6@00
                            (mod
                              (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                              step@8@00))
                          (<
                            (mod
                              (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                              step@8@00)
                            hi@7@00)))))))
              (< $Perm.No $k@49@00))
            (ite
              (and
                (<=
                  min@9@00
                  (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
                (implies
                  (<=
                    min@9@00
                    (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
                  (and
                    (<
                      (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                      max@10@00)
                    (implies
                      (<
                        (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                        max@10@00)
                      (and
                        (<=
                          lo@6@00
                          (mod
                            (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                            step@8@00))
                        (implies
                          (<=
                            lo@6@00
                            (mod
                              (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                              step@8@00))
                          (<
                            (mod
                              (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                              step@8@00)
                            hi@7@00)))))))
              (< $Perm.No $k@40@00)
              false))
          (=
            ($FVF.lookup_Ref__Integer_value (sm@52@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r))
        :qid |qp.fvfValDef2|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (ite
            (and
              (<=
                min@9@00
                (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
              (implies
                (<=
                  min@9@00
                  (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
                (and
                  (<
                    (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                    max@10@00)
                  (implies
                    (<
                      (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                      max@10@00)
                    (and
                      (<=
                        lo@6@00
                        (mod
                          (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                          step@8@00))
                      (implies
                        (<=
                          lo@6@00
                          (mod
                            (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                            step@8@00))
                        (<
                          (mod
                            (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                            step@8@00)
                          hi@7@00)))))))
            (< $Perm.No $k@40@00)
            false)
          (=
            ($FVF.lookup_Ref__Integer_value (sm@44@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (sm@44@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00) r))
        :qid |qp.fvfValDef0|))
      (forall ((r $Ref)) (!
        (implies
          (ite
            (and
              (<=
                min@9@00
                (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
              (implies
                (<=
                  min@9@00
                  (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
                (and
                  (<
                    (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                    max@10@00)
                  (implies
                    (<
                      (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                      max@10@00)
                    (and
                      (<=
                        lo@6@00
                        (mod
                          (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                          step@8@00))
                      (implies
                        (<=
                          lo@6@00
                          (mod
                            (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                            step@8@00))
                        (<
                          (mod
                            (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                            step@8@00)
                          hi@7@00)))))))
            (< $Perm.No $k@40@00)
            false)
          (=
            ($FVF.lookup_Ref__Integer_value (sm@44@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r))
        :qid |qp.fvfValDef0|)))
    (forall ((k@45@00 Int)) (!
      (implies
        (and
          (and
            (<= min@9@00 k@45@00)
            (implies
              (<= min@9@00 k@45@00)
              (and
                (< k@45@00 max@10@00)
                (implies
                  (< k@45@00 max@10@00)
                  (and
                    (<= lo@6@00 (mod k@45@00 step@8@00))
                    (implies
                      (<= lo@6@00 (mod k@45@00 step@8@00))
                      (< (mod k@45@00 step@8@00) hi@7@00)))))))
          (< $Perm.No $k@49@00))
        (=
          (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 ($Seq.index
            ar@11@00
            k@45@00))
          k@45@00))
      :pattern (($Seq.index ar@11@00 k@45@00))
      :qid |Ref__Integer_value-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (<=
              min@9@00
              (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
            (implies
              (<=
                min@9@00
                (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
              (and
                (<
                  (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                  max@10@00)
                (implies
                  (<
                    (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                    max@10@00)
                  (and
                    (<=
                      lo@6@00
                      (mod
                        (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                        step@8@00))
                    (implies
                      (<=
                        lo@6@00
                        (mod
                          (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                          step@8@00))
                      (<
                        (mod
                          (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                          step@8@00)
                        hi@7@00)))))))
          (< $Perm.No $k@49@00))
        (=
          ($Seq.index
            ar@11@00
            (inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
          r))
      :pattern ((inv@50@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
      :qid |Ref__Integer_value-fctOfInv|))
    (forall ((k@36@00 Int)) (!
      (implies
        (and
          (and
            (<= min@9@00 k@36@00)
            (implies
              (<= min@9@00 k@36@00)
              (and
                (< k@36@00 max@10@00)
                (implies
                  (< k@36@00 max@10@00)
                  (and
                    (<= lo@6@00 (mod k@36@00 step@8@00))
                    (implies
                      (<= lo@6@00 (mod k@36@00 step@8@00))
                      (< (mod k@36@00 step@8@00) hi@7@00)))))))
          (< $Perm.No $k@40@00))
        (=
          (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 ($Seq.index
            ar@11@00
            k@36@00))
          k@36@00))
      :pattern (($Seq.index ar@11@00 k@36@00))
      :qid |Ref__Integer_value-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (<=
              min@9@00
              (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
            (implies
              (<=
                min@9@00
                (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
              (and
                (<
                  (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                  max@10@00)
                (implies
                  (<
                    (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                    max@10@00)
                  (and
                    (<=
                      lo@6@00
                      (mod
                        (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                        step@8@00))
                    (implies
                      (<=
                        lo@6@00
                        (mod
                          (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                          step@8@00))
                      (<
                        (mod
                          (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r)
                          step@8@00)
                        hi@7@00)))))))
          (< $Perm.No $k@40@00))
        (=
          ($Seq.index
            ar@11@00
            (inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
          r))
      :pattern ((inv@41@00 s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00 r))
      :qid |Ref__Integer_value-fctOfInv|))))
  :pattern ((count_square s@$ i@5@00 lo@6@00 hi@7@00 step@8@00 min@9@00 max@10@00 ar@11@00 v@12@00))
  )))
(assert (forall ((s@$ $Snap) (i@14@00 Int) (lo@15@00 Int) (hi@16@00 Int) (step@17@00 Int) (min@18@00 Int) (max@19@00 Int) (ar@20@00 $Seq<$Ref>)) (!
  (=
    (sum_square%limited s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00)
    (sum_square s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00))
  :pattern ((sum_square s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00))
  )))
(assert (forall ((s@$ $Snap) (i@14@00 Int) (lo@15@00 Int) (hi@16@00 Int) (step@17@00 Int) (min@18@00 Int) (max@19@00 Int) (ar@20@00 $Seq<$Ref>)) (!
  (sum_square%stateless i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00)
  :pattern ((sum_square%limited s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00))
  )))
(assert (forall ((s@$ $Snap) (i@14@00 Int) (lo@15@00 Int) (hi@16@00 Int) (step@17@00 Int) (min@18@00 Int) (max@19@00 Int) (ar@20@00 $Seq<$Ref>)) (!
  (let ((result@21@00 (sum_square%limited s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00))) (and
    (implies
      (and
        (and
          (<= 0 lo@15@00)
          (and
            (<= lo@15@00 hi@16@00)
            (and (<= hi@16@00 step@17@00) (> step@17@00 0))))
        (and
          (<= 0 min@18@00)
          (and (<= min@18@00 i@14@00) (<= i@14@00 max@19@00)))
        (<= max@19@00 ($Seq.length ar@20@00)))
      (=
        (sum_square s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00)
        (ite
          (< i@14@00 max@19@00)
          (+
            (ite
              (and
                (<= lo@15@00 (mod i@14@00 step@17@00))
                (< (mod i@14@00 step@17@00) hi@16@00))
              ($FVF.lookup_Ref__Integer_value (sm@60@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00) ($Seq.index
                ar@20@00
                i@14@00))
              0)
            (sum_square%limited ($Snap.combine
              $Snap.unit
              ($Snap.combine
                $Snap.unit
                ($Snap.combine
                  $Snap.unit
                  ($Snap.combine
                    $Snap.unit
                    ($Snap.combine
                      $Snap.unit
                      ($Snap.combine
                        $Snap.unit
                        ($Snap.combine
                          $Snap.unit
                          ($Snap.combine
                            $Snap.unit
                            ($SortWrappers.$FVF<Int>To$Snap (sm@68@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00)))))))))) (+
              i@14@00
              1) lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00))
          0)))
    ($Perm.isReadVar $k@65@00 $Perm.Write)
    ($Perm.isReadVar $k@57@00 $Perm.Write)
    (forall ((r $Ref)) (!
      (iff
        (Set_in r ($FVF.domain_Ref__Integer_value (sm@68@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00)))
        (and
          (and
            (<=
              min@18@00
              (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
            (implies
              (<=
                min@18@00
                (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
              (and
                (<
                  (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                  max@19@00)
                (implies
                  (<
                    (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                    max@19@00)
                  (and
                    (<=
                      lo@15@00
                      (mod
                        (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                        step@17@00))
                    (implies
                      (<=
                        lo@15@00
                        (mod
                          (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                          step@17@00))
                      (<
                        (mod
                          (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                          step@17@00)
                        hi@16@00)))))))
          (< $Perm.No $k@65@00)))
      :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (sm@68@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00))))
      :qid |qp.fvfDomDef7|))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            (and
              (and
                (<=
                  min@18@00
                  (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
                (implies
                  (<=
                    min@18@00
                    (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
                  (and
                    (<
                      (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                      max@19@00)
                    (implies
                      (<
                        (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                        max@19@00)
                      (and
                        (<=
                          lo@15@00
                          (mod
                            (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                            step@17@00))
                        (implies
                          (<=
                            lo@15@00
                            (mod
                              (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                              step@17@00))
                          (<
                            (mod
                              (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                              step@17@00)
                            hi@16@00)))))))
              (< $Perm.No $k@65@00))
            (ite
              (and
                (<=
                  min@18@00
                  (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
                (implies
                  (<=
                    min@18@00
                    (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
                  (and
                    (<
                      (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                      max@19@00)
                    (implies
                      (<
                        (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                        max@19@00)
                      (and
                        (<=
                          lo@15@00
                          (mod
                            (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                            step@17@00))
                        (implies
                          (<=
                            lo@15@00
                            (mod
                              (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                              step@17@00))
                          (<
                            (mod
                              (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                              step@17@00)
                            hi@16@00)))))))
              (< $Perm.No $k@57@00)
              false))
          (=
            ($FVF.lookup_Ref__Integer_value (sm@68@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (sm@68@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00) r))
        :qid |qp.fvfValDef6|))
      (forall ((r $Ref)) (!
        (implies
          (and
            (and
              (and
                (<=
                  min@18@00
                  (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
                (implies
                  (<=
                    min@18@00
                    (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
                  (and
                    (<
                      (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                      max@19@00)
                    (implies
                      (<
                        (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                        max@19@00)
                      (and
                        (<=
                          lo@15@00
                          (mod
                            (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                            step@17@00))
                        (implies
                          (<=
                            lo@15@00
                            (mod
                              (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                              step@17@00))
                          (<
                            (mod
                              (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                              step@17@00)
                            hi@16@00)))))))
              (< $Perm.No $k@65@00))
            (ite
              (and
                (<=
                  min@18@00
                  (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
                (implies
                  (<=
                    min@18@00
                    (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
                  (and
                    (<
                      (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                      max@19@00)
                    (implies
                      (<
                        (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                        max@19@00)
                      (and
                        (<=
                          lo@15@00
                          (mod
                            (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                            step@17@00))
                        (implies
                          (<=
                            lo@15@00
                            (mod
                              (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                              step@17@00))
                          (<
                            (mod
                              (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                              step@17@00)
                            hi@16@00)))))))
              (< $Perm.No $k@57@00)
              false))
          (=
            ($FVF.lookup_Ref__Integer_value (sm@68@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r))
        :qid |qp.fvfValDef6|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (ite
            (and
              (<=
                min@18@00
                (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
              (implies
                (<=
                  min@18@00
                  (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
                (and
                  (<
                    (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                    max@19@00)
                  (implies
                    (<
                      (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                      max@19@00)
                    (and
                      (<=
                        lo@15@00
                        (mod
                          (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                          step@17@00))
                      (implies
                        (<=
                          lo@15@00
                          (mod
                            (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                            step@17@00))
                        (<
                          (mod
                            (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                            step@17@00)
                          hi@16@00)))))))
            (< $Perm.No $k@57@00)
            false)
          (=
            ($FVF.lookup_Ref__Integer_value (sm@60@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (sm@60@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00) r))
        :qid |qp.fvfValDef4|))
      (forall ((r $Ref)) (!
        (implies
          (ite
            (and
              (<=
                min@18@00
                (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
              (implies
                (<=
                  min@18@00
                  (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
                (and
                  (<
                    (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                    max@19@00)
                  (implies
                    (<
                      (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                      max@19@00)
                    (and
                      (<=
                        lo@15@00
                        (mod
                          (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                          step@17@00))
                      (implies
                        (<=
                          lo@15@00
                          (mod
                            (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                            step@17@00))
                        (<
                          (mod
                            (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                            step@17@00)
                          hi@16@00)))))))
            (< $Perm.No $k@57@00)
            false)
          (=
            ($FVF.lookup_Ref__Integer_value (sm@60@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r))
        :qid |qp.fvfValDef4|)))
    (forall ((k@61@00 Int)) (!
      (implies
        (and
          (and
            (<= min@18@00 k@61@00)
            (implies
              (<= min@18@00 k@61@00)
              (and
                (< k@61@00 max@19@00)
                (implies
                  (< k@61@00 max@19@00)
                  (and
                    (<= lo@15@00 (mod k@61@00 step@17@00))
                    (implies
                      (<= lo@15@00 (mod k@61@00 step@17@00))
                      (< (mod k@61@00 step@17@00) hi@16@00)))))))
          (< $Perm.No $k@65@00))
        (=
          (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 ($Seq.index
            ar@20@00
            k@61@00))
          k@61@00))
      :pattern (($Seq.index ar@20@00 k@61@00))
      :qid |Ref__Integer_value-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (<=
              min@18@00
              (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
            (implies
              (<=
                min@18@00
                (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
              (and
                (<
                  (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                  max@19@00)
                (implies
                  (<
                    (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                    max@19@00)
                  (and
                    (<=
                      lo@15@00
                      (mod
                        (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                        step@17@00))
                    (implies
                      (<=
                        lo@15@00
                        (mod
                          (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                          step@17@00))
                      (<
                        (mod
                          (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                          step@17@00)
                        hi@16@00)))))))
          (< $Perm.No $k@65@00))
        (=
          ($Seq.index
            ar@20@00
            (inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
          r))
      :pattern ((inv@66@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
      :qid |Ref__Integer_value-fctOfInv|))
    (forall ((k@53@00 Int)) (!
      (implies
        (and
          (and
            (<= min@18@00 k@53@00)
            (implies
              (<= min@18@00 k@53@00)
              (and
                (< k@53@00 max@19@00)
                (implies
                  (< k@53@00 max@19@00)
                  (and
                    (<= lo@15@00 (mod k@53@00 step@17@00))
                    (implies
                      (<= lo@15@00 (mod k@53@00 step@17@00))
                      (< (mod k@53@00 step@17@00) hi@16@00)))))))
          (< $Perm.No $k@57@00))
        (=
          (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 ($Seq.index
            ar@20@00
            k@53@00))
          k@53@00))
      :pattern (($Seq.index ar@20@00 k@53@00))
      :qid |Ref__Integer_value-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (<=
              min@18@00
              (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
            (implies
              (<=
                min@18@00
                (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
              (and
                (<
                  (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                  max@19@00)
                (implies
                  (<
                    (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                    max@19@00)
                  (and
                    (<=
                      lo@15@00
                      (mod
                        (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                        step@17@00))
                    (implies
                      (<=
                        lo@15@00
                        (mod
                          (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                          step@17@00))
                      (<
                        (mod
                          (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r)
                          step@17@00)
                        hi@16@00)))))))
          (< $Perm.No $k@57@00))
        (=
          ($Seq.index
            ar@20@00
            (inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
          r))
      :pattern ((inv@58@00 s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00 r))
      :qid |Ref__Integer_value-fctOfInv|))))
  :pattern ((sum_square s@$ i@14@00 lo@15@00 hi@16@00 step@17@00 min@18@00 max@19@00 ar@20@00))
  )))
(assert (forall ((s@$ $Snap) (i@22@00 Int) (hi@23@00 Int) (ar@24@00 $Seq<Int>)) (!
  (=
    (sum_list%limited s@$ i@22@00 hi@23@00 ar@24@00)
    (sum_list s@$ i@22@00 hi@23@00 ar@24@00))
  :pattern ((sum_list s@$ i@22@00 hi@23@00 ar@24@00))
  )))
(assert (forall ((s@$ $Snap) (i@22@00 Int) (hi@23@00 Int) (ar@24@00 $Seq<Int>)) (!
  (sum_list%stateless i@22@00 hi@23@00 ar@24@00)
  :pattern ((sum_list%limited s@$ i@22@00 hi@23@00 ar@24@00))
  )))
(assert (forall ((s@$ $Snap) (i@22@00 Int) (hi@23@00 Int) (ar@24@00 $Seq<Int>)) (!
  (let ((result@25@00 (sum_list%limited s@$ i@22@00 hi@23@00 ar@24@00))) (implies
    (and
      (and (<= 0 i@22@00) (<= i@22@00 hi@23@00))
      (<= hi@23@00 ($Seq.length ar@24@00)))
    (=
      (sum_list s@$ i@22@00 hi@23@00 ar@24@00)
      (ite
        (< i@22@00 hi@23@00)
        (+
          ($Seq.index ar@24@00 i@22@00)
          (sum_list%limited ($Snap.combine
            $Snap.unit
            ($Snap.combine $Snap.unit $Snap.unit)) (+ i@22@00 1) hi@23@00 ar@24@00))
        0))))
  :pattern ((sum_list s@$ i@22@00 hi@23@00 ar@24@00))
  )))
(assert (forall ((s@$ $Snap) (i@26@00 Int) (lo@27@00 Int) (hi@28@00 Int) (ar@29@00 $Seq<$Ref>)) (!
  (=
    (sum_array%limited s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00)
    (sum_array s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00))
  :pattern ((sum_array s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00))
  )))
(assert (forall ((s@$ $Snap) (i@26@00 Int) (lo@27@00 Int) (hi@28@00 Int) (ar@29@00 $Seq<$Ref>)) (!
  (sum_array%stateless i@26@00 lo@27@00 hi@28@00 ar@29@00)
  :pattern ((sum_array%limited s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00))
  )))
(assert (forall ((s@$ $Snap) (i@26@00 Int) (lo@27@00 Int) (hi@28@00 Int) (ar@29@00 $Seq<$Ref>)) (!
  (let ((result@30@00 (sum_array%limited s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00))) (and
    (implies
      (and
        (and (<= 0 lo@27@00) (and (<= lo@27@00 i@26@00) (<= i@26@00 hi@28@00)))
        (<= hi@28@00 ($Seq.length ar@29@00)))
      (=
        (sum_array s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00)
        (ite
          (< i@26@00 hi@28@00)
          (+
            ($FVF.lookup_Ref__Integer_value (sm@72@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00) ($Seq.index
              ar@29@00
              i@26@00))
            (sum_array%limited ($Snap.combine
              $Snap.unit
              ($Snap.combine
                $Snap.unit
                ($Snap.combine
                  $Snap.unit
                  ($Snap.combine
                    $Snap.unit
                    ($SortWrappers.$FVF<Int>To$Snap (sm@77@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00)))))) (+
              i@26@00
              1) lo@27@00 hi@28@00 ar@29@00))
          0)))
    ($Perm.isReadVar $k@74@00 $Perm.Write)
    ($Perm.isReadVar $k@70@00 $Perm.Write)
    (forall ((r $Ref)) (!
      (iff
        (Set_in r ($FVF.domain_Ref__Integer_value (sm@77@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00)))
        (and
          ($Seq.contains
            ($Seq.range lo@27@00 hi@28@00)
            (inv@75@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
          (< $Perm.No $k@74@00)))
      :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (sm@77@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00))))
      :qid |qp.fvfDomDef11|))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            (and
              ($Seq.contains
                ($Seq.range lo@27@00 hi@28@00)
                (inv@75@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
              (< $Perm.No $k@74@00))
            (ite
              ($Seq.contains
                ($Seq.range lo@27@00 hi@28@00)
                (inv@71@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
              (< $Perm.No $k@70@00)
              false))
          (=
            ($FVF.lookup_Ref__Integer_value (sm@77@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (sm@77@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00) r))
        :qid |qp.fvfValDef10|))
      (forall ((r $Ref)) (!
        (implies
          (and
            (and
              ($Seq.contains
                ($Seq.range lo@27@00 hi@28@00)
                (inv@75@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
              (< $Perm.No $k@74@00))
            (ite
              ($Seq.contains
                ($Seq.range lo@27@00 hi@28@00)
                (inv@71@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
              (< $Perm.No $k@70@00)
              false))
          (=
            ($FVF.lookup_Ref__Integer_value (sm@77@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))) r))
        :qid |qp.fvfValDef10|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (ite
            ($Seq.contains
              ($Seq.range lo@27@00 hi@28@00)
              (inv@71@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
            (< $Perm.No $k@70@00)
            false)
          (=
            ($FVF.lookup_Ref__Integer_value (sm@72@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (sm@72@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00) r))
        :qid |qp.fvfValDef8|))
      (forall ((r $Ref)) (!
        (implies
          (ite
            ($Seq.contains
              ($Seq.range lo@27@00 hi@28@00)
              (inv@71@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
            (< $Perm.No $k@70@00)
            false)
          (=
            ($FVF.lookup_Ref__Integer_value (sm@72@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))) r))
        :qid |qp.fvfValDef8|)))
    (forall ((k@73@00 Int)) (!
      (implies
        (and
          ($Seq.contains ($Seq.range lo@27@00 hi@28@00) k@73@00)
          (< $Perm.No $k@74@00))
        (=
          (inv@75@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 ($Seq.index
            ar@29@00
            k@73@00))
          k@73@00))
      :pattern (($Seq.index ar@29@00 k@73@00))
      :qid |Ref__Integer_value-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (and
          ($Seq.contains
            ($Seq.range lo@27@00 hi@28@00)
            (inv@75@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
          (< $Perm.No $k@74@00))
        (=
          ($Seq.index
            ar@29@00
            (inv@75@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
          r))
      :pattern ((inv@75@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
      :qid |Ref__Integer_value-fctOfInv|))
    (forall ((k@69@00 Int)) (!
      (implies
        (and
          ($Seq.contains ($Seq.range lo@27@00 hi@28@00) k@69@00)
          (< $Perm.No $k@70@00))
        (=
          (inv@71@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 ($Seq.index
            ar@29@00
            k@69@00))
          k@69@00))
      :pattern (($Seq.index ar@29@00 k@69@00))
      :qid |Ref__Integer_value-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (and
          ($Seq.contains
            ($Seq.range lo@27@00 hi@28@00)
            (inv@71@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
          (< $Perm.No $k@70@00))
        (=
          ($Seq.index
            ar@29@00
            (inv@71@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
          r))
      :pattern ((inv@71@00 s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00 r))
      :qid |Ref__Integer_value-fctOfInv|))))
  :pattern ((sum_array s@$ i@26@00 lo@27@00 hi@28@00 ar@29@00))
  )))
(assert (forall ((s@$ $Snap) (i@31@00 Int) (hi@32@00 Int) (ar@33@00 $Seq<$Ref>) (v@34@00 Int)) (!
  (=
    (count_array%limited s@$ i@31@00 hi@32@00 ar@33@00 v@34@00)
    (count_array s@$ i@31@00 hi@32@00 ar@33@00 v@34@00))
  :pattern ((count_array s@$ i@31@00 hi@32@00 ar@33@00 v@34@00))
  )))
(assert (forall ((s@$ $Snap) (i@31@00 Int) (hi@32@00 Int) (ar@33@00 $Seq<$Ref>) (v@34@00 Int)) (!
  (count_array%stateless i@31@00 hi@32@00 ar@33@00 v@34@00)
  :pattern ((count_array%limited s@$ i@31@00 hi@32@00 ar@33@00 v@34@00))
  )))
(assert (forall ((s@$ $Snap) (i@31@00 Int) (hi@32@00 Int) (ar@33@00 $Seq<$Ref>) (v@34@00 Int)) (!
  (let ((result@35@00 (count_array%limited s@$ i@31@00 hi@32@00 ar@33@00 v@34@00))) (and
    (implies
      (and
        (and (<= 0 i@31@00) (<= i@31@00 hi@32@00))
        (<= hi@32@00 ($Seq.length ar@33@00)))
      (=
        (count_array s@$ i@31@00 hi@32@00 ar@33@00 v@34@00)
        (ite
          (< i@31@00 hi@32@00)
          (+
            (ite
              (=
                ($FVF.lookup_Ref__Integer_value (sm@81@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00) ($Seq.index
                  ar@33@00
                  i@31@00))
                v@34@00)
              1
              0)
            (count_array%limited ($Snap.combine
              $Snap.unit
              ($Snap.combine
                $Snap.unit
                ($Snap.combine
                  $Snap.unit
                  ($SortWrappers.$FVF<Int>To$Snap (sm@86@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00))))) (+
              i@31@00
              1) hi@32@00 ar@33@00 v@34@00))
          0)))
    ($Perm.isReadVar $k@83@00 $Perm.Write)
    ($Perm.isReadVar $k@79@00 $Perm.Write)
    (forall ((r $Ref)) (!
      (iff
        (Set_in r ($FVF.domain_Ref__Integer_value (sm@86@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00)))
        (and
          ($Seq.contains
            ($Seq.range 0 hi@32@00)
            (inv@84@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
          (< $Perm.No $k@83@00)))
      :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (sm@86@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00))))
      :qid |qp.fvfDomDef15|))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            (and
              ($Seq.contains
                ($Seq.range 0 hi@32@00)
                (inv@84@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
              (< $Perm.No $k@83@00))
            (ite
              ($Seq.contains
                ($Seq.range 0 hi@32@00)
                (inv@80@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
              (< $Perm.No $k@79@00)
              false))
          (=
            ($FVF.lookup_Ref__Integer_value (sm@86@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second s@$)))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (sm@86@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00) r))
        :qid |qp.fvfValDef14|))
      (forall ((r $Ref)) (!
        (implies
          (and
            (and
              ($Seq.contains
                ($Seq.range 0 hi@32@00)
                (inv@84@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
              (< $Perm.No $k@83@00))
            (ite
              ($Seq.contains
                ($Seq.range 0 hi@32@00)
                (inv@80@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
              (< $Perm.No $k@79@00)
              false))
          (=
            ($FVF.lookup_Ref__Integer_value (sm@86@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second s@$)))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second s@$)))) r))
        :qid |qp.fvfValDef14|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (ite
            ($Seq.contains
              ($Seq.range 0 hi@32@00)
              (inv@80@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
            (< $Perm.No $k@79@00)
            false)
          (=
            ($FVF.lookup_Ref__Integer_value (sm@81@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second s@$)))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (sm@81@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00) r))
        :qid |qp.fvfValDef12|))
      (forall ((r $Ref)) (!
        (implies
          (ite
            ($Seq.contains
              ($Seq.range 0 hi@32@00)
              (inv@80@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
            (< $Perm.No $k@79@00)
            false)
          (=
            ($FVF.lookup_Ref__Integer_value (sm@81@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00) r)
            ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second s@$)))) r)))
        :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.second ($Snap.second ($Snap.second s@$)))) r))
        :qid |qp.fvfValDef12|)))
    (forall ((k@82@00 Int)) (!
      (implies
        (and
          ($Seq.contains ($Seq.range 0 hi@32@00) k@82@00)
          (< $Perm.No $k@83@00))
        (=
          (inv@84@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 ($Seq.index
            ar@33@00
            k@82@00))
          k@82@00))
      :pattern (($Seq.index ar@33@00 k@82@00))
      :qid |Ref__Integer_value-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (and
          ($Seq.contains
            ($Seq.range 0 hi@32@00)
            (inv@84@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
          (< $Perm.No $k@83@00))
        (=
          ($Seq.index
            ar@33@00
            (inv@84@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
          r))
      :pattern ((inv@84@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
      :qid |Ref__Integer_value-fctOfInv|))
    (forall ((k@78@00 Int)) (!
      (implies
        (and
          ($Seq.contains ($Seq.range 0 hi@32@00) k@78@00)
          (< $Perm.No $k@79@00))
        (=
          (inv@80@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 ($Seq.index
            ar@33@00
            k@78@00))
          k@78@00))
      :pattern (($Seq.index ar@33@00 k@78@00))
      :qid |Ref__Integer_value-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (and
          ($Seq.contains
            ($Seq.range 0 hi@32@00)
            (inv@80@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
          (< $Perm.No $k@79@00))
        (=
          ($Seq.index
            ar@33@00
            (inv@80@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
          r))
      :pattern ((inv@80@00 s@$ i@31@00 hi@32@00 ar@33@00 v@34@00 r))
      :qid |Ref__Integer_value-fctOfInv|))))
  :pattern ((count_array s@$ i@31@00 hi@32@00 ar@33@00 v@34@00))
  )))
; End function- and predicate-related preamble
; ------------------------------------------------------------
; ---------- Ref__loop_main_93 ----------
(declare-const diz@0@01 $Ref)
(declare-const P@1@01 Int)
(declare-const hist@2@01 $Seq<$Ref>)
(declare-const diz@3@01 $Ref)
(declare-const P@4@01 Int)
(declare-const hist@5@01 $Seq<$Ref>)
(push) ; 1
(declare-const $t@6@01 $Snap)
(declare-const $t@7@01 $Snap)
(assert (= $t@6@01 ($Snap.combine $Snap.unit $t@7@01)))
; [eval] diz != null
(assert (not (= diz@3@01 $Ref.null)))
(declare-const $t@8@01 $FVF<Int>)
(assert (= $t@7@01 ($Snap.combine $Snap.unit ($SortWrappers.$FVF<Int>To$Snap $t@8@01))))
; [eval] P <= |hist|
; [eval] |hist|
(assert (<= P@4@01 ($Seq.length hist@5@01)))
(declare-const k@9@01 Int)
(push) ; 2
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@4@01) k@9@01))
; [eval] hist[k]
;(set-option :timeout 0)
(push) ; 3
(assert (not (>= k@9@01 0)))
 (set-option :rlimit 69342) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (< k@9@01 ($Seq.length hist@5@01))))
 (set-option :rlimit 19501) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(pop) ; 2
(declare-fun inv@10@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((k@9@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@4@01) k@9@01)
    (= (inv@10@01 ($Seq.index hist@5@01 k@9@01)) k@9@01))
  :pattern (($Seq.index hist@5@01 k@9@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@4@01) (inv@10@01 r))
    (= ($Seq.index hist@5@01 (inv@10@01 r)) r))
  :pattern ((inv@10@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((k@9@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@4@01) k@9@01)
    (not (= ($Seq.index hist@5@01 k@9@01) $Ref.null)))
  :pattern (($Seq.index hist@5@01 k@9@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
; State saturation: after contract
;(set-option :timeout 50)
 (set-option :rlimit 68541) (check-sat) 
; unknown
(push) ; 2
(declare-const $t@11@01 $Snap)
(declare-const $t@12@01 $FVF<Int>)
(assert (= $t@11@01 ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@12@01) $Snap.unit)))
(declare-const k@13@01 Int)
(push) ; 3
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@4@01) k@13@01))
; [eval] hist[k]
;(set-option :timeout 0)
(push) ; 4
(assert (not (>= k@13@01 0)))
 (set-option :rlimit 25170) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< k@13@01 ($Seq.length hist@5@01))))
 (set-option :rlimit 11737) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@14@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((k@13@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@4@01) k@13@01)
    (= (inv@14@01 ($Seq.index hist@5@01 k@13@01)) k@13@01))
  :pattern (($Seq.index hist@5@01 k@13@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@4@01) (inv@14@01 r))
    (= ($Seq.index hist@5@01 (inv@14@01 r)) r))
  :pattern ((inv@14@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((k@13@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@4@01) k@13@01)
    (not (= ($Seq.index hist@5@01 k@13@01) $Ref.null)))
  :pattern (($Seq.index hist@5@01 k@13@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
; [eval] (forall k: Int :: { (k in [0..P)) } { hist[k] } (k in [0..P)) ==> hist[k].Ref__Integer_value == 0)
(declare-const k@15@01 Int)
(push) ; 3
; [eval] (k in [0..P)) ==> hist[k].Ref__Integer_value == 0
; [eval] (k in [0..P))
; [eval] [0..P)
(push) ; 4
; [then-branch: 0 | k@15@01 in [0..P@4@01] | live]
; [else-branch: 0 | !k@15@01 in [0..P@4@01] | live]
(push) ; 5
; [then-branch: 0 | k@15@01 in [0..P@4@01]]
(assert ($Seq.contains ($Seq.range 0 P@4@01) k@15@01))
; [eval] hist[k].Ref__Integer_value == 0
; [eval] hist[k]
(push) ; 6
(assert (not (>= k@15@01 0)))
 (set-option :rlimit 1987) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k@15@01 ($Seq.length hist@5@01))))
 (set-option :rlimit 157286) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not ($Seq.contains ($Seq.range 0 P@4@01) (inv@14@01 ($Seq.index hist@5@01 k@15@01)))))
 (set-option :rlimit 223912) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(declare-const sm@16@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@4@01) (inv@14@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@12@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r))
    :qid |qp.fvfValDef0|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@4@01) (inv@14@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@12@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@12@01 r))
    :qid |qp.fvfValDef0|))))
(pop) ; 5
(push) ; 5
; [else-branch: 0 | !k@15@01 in [0..P@4@01]]
(assert (not ($Seq.contains ($Seq.range 0 P@4@01) k@15@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (implies
  ($Seq.contains ($Seq.range 0 P@4@01) k@15@01)
  (and
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@4@01) (inv@14@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@12@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r))
        :qid |qp.fvfValDef0|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@4@01) (inv@14@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@12@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@12@01 r))
        :qid |qp.fvfValDef0|)))
    ($Seq.contains ($Seq.range 0 P@4@01) k@15@01))))
; Joined path conditions
(pop) ; 3
; Nested auxiliary terms
(assert (forall ((k@15@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@4@01) k@15@01)
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@4@01) (inv@14@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@12@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r))
          :qid |qp.fvfValDef0|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@4@01) (inv@14@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@12@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@12@01 r))
          :qid |qp.fvfValDef0|)))
      ($Seq.contains ($Seq.range 0 P@4@01) k@15@01)))
  :pattern (($Seq.contains ($Seq.range 0 P@4@01) k@15@01))
  :qid |prog.l56-aux|)))
(assert (forall ((k@15@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@4@01) k@15@01)
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@4@01) (inv@14@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@12@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r))
          :qid |qp.fvfValDef0|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@4@01) (inv@14@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@12@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@12@01 r))
          :qid |qp.fvfValDef0|)))
      ($Seq.contains ($Seq.range 0 P@4@01) k@15@01)))
  :pattern (($Seq.index hist@5@01 k@15@01))
  :qid |prog.l56-aux|)))
(assert (and
  (forall ((k@15@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@4@01) k@15@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) ($Seq.index
          hist@5@01
          k@15@01))
        0))
    :pattern (($Seq.contains ($Seq.range 0 P@4@01) k@15@01))
    :qid |prog.l56|))
  (forall ((k@15@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@4@01) k@15@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@16@01  $FVF<Int>) ($Seq.index
          hist@5@01
          k@15@01))
        0))
    :pattern (($Seq.index hist@5@01 k@15@01))
    :qid |prog.l56|))))
(pop) ; 2
(push) ; 2
; [exec]
; inhale false
(pop) ; 2
(pop) ; 1
; ---------- Ref__loop_body_93 ----------
(declare-const diz@17@01 $Ref)
(declare-const k@18@01 Int)
(declare-const P@19@01 Int)
(declare-const hist@20@01 $Seq<$Ref>)
(declare-const diz@21@01 $Ref)
(declare-const k@22@01 Int)
(declare-const P@23@01 Int)
(declare-const hist@24@01 $Seq<$Ref>)
(push) ; 1
(declare-const $t@25@01 $Snap)
(declare-const $t@26@01 $Snap)
(assert (= $t@25@01 ($Snap.combine $Snap.unit $t@26@01)))
; [eval] diz != null
(assert (not (= diz@21@01 $Ref.null)))
(declare-const $t@27@01 $Snap)
(assert (= $t@26@01 ($Snap.combine $Snap.unit $t@27@01)))
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@23@01) k@22@01))
(declare-const $t@28@01 Int)
(assert (= $t@27@01 ($Snap.combine $Snap.unit ($SortWrappers.IntTo$Snap $t@28@01))))
; [eval] P <= |hist|
; [eval] |hist|
(assert (<= P@23@01 ($Seq.length hist@24@01)))
; [eval] hist[k]
(push) ; 2
(assert (not (>= k@22@01 0)))
 (set-option :rlimit 4010) (check-sat) 
; unsat
(pop) ; 2
; 0.00s
; 
(push) ; 2
(assert (not (< k@22@01 ($Seq.length hist@24@01))))
 (set-option :rlimit 173986) (check-sat) 
; unsat
(pop) ; 2
; 0.00s
; 
(assert (not (= ($Seq.index hist@24@01 k@22@01) $Ref.null)))
; State saturation: after contract
;(set-option :timeout 50)
 (set-option :rlimit 420826) (check-sat) 
; unknown
(push) ; 2
(declare-const $t@29@01 $Snap)
(declare-const $t@30@01 $Snap)
(assert (= $t@29@01 ($Snap.combine $Snap.unit $t@30@01)))
; [eval] (k in [0..P))
; [eval] [0..P)
(declare-const $t@31@01 Int)
(assert (= $t@30@01 ($Snap.combine ($SortWrappers.IntTo$Snap $t@31@01) $Snap.unit)))
; [eval] hist[k]
;(set-option :timeout 0)
(push) ; 3
(assert (not (>= k@22@01 0)))
 (set-option :rlimit 24575) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (< k@22@01 ($Seq.length hist@24@01))))
 (set-option :rlimit 13067) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; [eval] hist[k].Ref__Integer_value == 0
; [eval] hist[k]
(push) ; 3
(assert (not (>= k@22@01 0)))
 (set-option :rlimit 6984) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (< k@22@01 ($Seq.length hist@24@01))))
 (set-option :rlimit 69529) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(assert (= $t@31@01 0))
(pop) ; 2
(push) ; 2
; [exec]
; var __flatten_3: Ref
(declare-const __flatten_3@32@01 $Ref)
; [exec]
; __flatten_3 := hist[k]
; [eval] hist[k]
(push) ; 3
(assert (not (>= k@22@01 0)))
 (set-option :rlimit 222002) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (< k@22@01 ($Seq.length hist@24@01))))
 (set-option :rlimit 87155) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; [exec]
; __flatten_3.Ref__Integer_value := 0
; [eval] (k in [0..P))
; [eval] [0..P)
; [eval] hist[k]
(push) ; 3
(assert (not (>= k@22@01 0)))
 (set-option :rlimit 23418) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (< k@22@01 ($Seq.length hist@24@01))))
 (set-option :rlimit 14656) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (or (= $Perm.Write $Perm.No) true)))
 (set-option :rlimit 40170) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; [eval] hist[k].Ref__Integer_value == 0
; [eval] hist[k]
(push) ; 3
(assert (not (>= k@22@01 0)))
 (set-option :rlimit 27509) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (< k@22@01 ($Seq.length hist@24@01))))
 (set-option :rlimit 73722) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(pop) ; 2
(pop) ; 1
; ---------- Ref__loop_main_113 ----------
(declare-const diz@33@01 $Ref)
(declare-const N@34@01 Int)
(declare-const M@35@01 Int)
(declare-const step@36@01 Int)
(declare-const hist@37@01 $Seq<$Ref>)
(declare-const matrix@38@01 $Seq<$Ref>)
(declare-const P@39@01 Int)
(declare-const diz@40@01 $Ref)
(declare-const N@41@01 Int)
(declare-const M@42@01 Int)
(declare-const step@43@01 Int)
(declare-const hist@44@01 $Seq<$Ref>)
(declare-const matrix@45@01 $Seq<$Ref>)
(declare-const P@46@01 Int)
(push) ; 1
(declare-const $t@47@01 $Snap)
(declare-const $t@48@01 $Snap)
(assert (= $t@47@01 ($Snap.combine $Snap.unit $t@48@01)))
; [eval] diz != null
(assert (not (= diz@40@01 $Ref.null)))
(declare-const $t@49@01 $Snap)
(assert (= $t@48@01 ($Snap.combine $Snap.unit $t@49@01)))
; [eval] M > 0
(assert (> M@42@01 0))
(declare-const $t@50@01 $Snap)
(assert (= $t@49@01 ($Snap.combine $Snap.unit $t@50@01)))
; [eval] N > 0
(assert (> N@41@01 0))
(declare-const $t@51@01 $Snap)
(assert (= $t@50@01 ($Snap.combine $Snap.unit $t@51@01)))
; [eval] step >= N
(assert (>= step@43@01 N@41@01))
(declare-const $t@52@01 $Snap)
(assert (= $t@51@01 ($Snap.combine $Snap.unit $t@52@01)))
; [eval] P > 0
(assert (> P@46@01 0))
(declare-const $t@53@01 $Snap)
(assert (= $t@52@01 ($Snap.combine $Snap.unit $t@53@01)))
; [eval] P <= |hist|
; [eval] |hist|
(assert (<= P@46@01 ($Seq.length hist@44@01)))
(declare-const $t@54@01 $FVF<Int>)
(declare-const $t@55@01 $Snap)
(assert (= $t@53@01 ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@54@01) $t@55@01)))
(declare-const k@56@01 Int)
(push) ; 2
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@46@01) k@56@01))
; [eval] hist[k]
(push) ; 3
(assert (not (>= k@56@01 0)))
 (set-option :rlimit 28450) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (< k@56@01 ($Seq.length hist@44@01))))
 (set-option :rlimit 31116) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(pop) ; 2
(declare-fun inv@57@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((k@56@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@46@01) k@56@01)
    (= (inv@57@01 ($Seq.index hist@44@01 k@56@01)) k@56@01))
  :pattern (($Seq.index hist@44@01 k@56@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
    (= ($Seq.index hist@44@01 (inv@57@01 r)) r))
  :pattern ((inv@57@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((k@56@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@46@01) k@56@01)
    (not (= ($Seq.index hist@44@01 k@56@01) $Ref.null)))
  :pattern (($Seq.index hist@44@01 k@56@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
(declare-const $t@58@01 $Snap)
(assert (= $t@55@01 ($Snap.combine $Snap.unit $t@58@01)))
; [eval] N <= step
(assert (<= N@41@01 step@43@01))
(declare-const $t@59@01 $Snap)
(assert (= $t@58@01 ($Snap.combine $Snap.unit $t@59@01)))
; [eval] M * step <= |matrix|
; [eval] M * step
; [eval] |matrix|
(assert (<= (* M@42@01 step@43@01) ($Seq.length matrix@45@01)))
(declare-const $t@60@01 $FVF<Int>)
(assert (= $t@59@01 ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@60@01) $Snap.unit)))
(declare-const j@61@01 Int)
(push) ; 2
; [eval] (j in [0..M * step)) && j % step < N
; [eval] (j in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@62@01 ==> j % step < N
(push) ; 3
; [then-branch: 1 | j@61@01 in [0..M@42@01 * step@43@01] | live]
; [else-branch: 1 | !j@61@01 in [0..M@42@01 * step@43@01] | live]
(push) ; 4
; [then-branch: 1 | j@61@01 in [0..M@42@01 * step@43@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@61@01))
; [eval] j % step < N
; [eval] j % step
(push) ; 5
(assert (not (not (= step@43@01 0))))
 (set-option :rlimit 2557) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(pop) ; 4
(push) ; 4
; [else-branch: 1 | !j@61@01 in [0..M@42@01 * step@43@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@61@01)))
(pop) ; 4
(pop) ; 3
; Joined path conditions
; Joined path conditions
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@61@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@61@01)
    (< (mod j@61@01 step@43@01) N@41@01))))
; [eval] matrix[j]
(push) ; 3
(assert (not (>= j@61@01 0)))
 (set-option :rlimit 17923) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (< j@61@01 ($Seq.length matrix@45@01))))
 (set-option :rlimit 46832) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (not (= 4 0))))
 (set-option :rlimit 11021) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(pop) ; 2
(declare-fun inv@63@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((j@61@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@61@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@61@01)
        (< (mod j@61@01 step@43@01) N@41@01)))
    (= (inv@63@01 ($Seq.index matrix@45@01 j@61@01)) j@61@01))
  :pattern (($Seq.index matrix@45@01 j@61@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
        (< (mod (inv@63@01 r) step@43@01) N@41@01)))
    (= ($Seq.index matrix@45@01 (inv@63@01 r)) r))
  :pattern ((inv@63@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j@61@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@61@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@61@01)
        (< (mod j@61@01 step@43@01) N@41@01)))
    (not (= ($Seq.index matrix@45@01 j@61@01) $Ref.null)))
  :pattern (($Seq.index matrix@45@01 j@61@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
; [eval] N <= step
; [eval] (forall k_fresh_rw_0: Int :: { (matrix[k_fresh_rw_0].Ref__Integer_value in [0..P)) } (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> (matrix[k_fresh_rw_0].Ref__Integer_value in [0..P)))
(declare-const k_fresh_rw_0@64@01 Int)
(push) ; 2
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> (matrix[k_fresh_rw_0].Ref__Integer_value in [0..P))
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N
; [eval] (k_fresh_rw_0 in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@65@01 ==> k_fresh_rw_0 % step < N
(push) ; 3
; [then-branch: 2 | k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01] | live]
; [else-branch: 2 | !k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01] | live]
(push) ; 4
; [then-branch: 2 | k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01))
; [eval] k_fresh_rw_0 % step < N
; [eval] k_fresh_rw_0 % step
(push) ; 5
(assert (not (not (= step@43@01 0))))
 (set-option :rlimit 95538) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(pop) ; 4
(push) ; 4
; [else-branch: 2 | !k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)))
(pop) ; 4
(pop) ; 3
; Joined path conditions
; Joined path conditions
(push) ; 3
; [then-branch: 3 | k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01] && k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01] ==> k_fresh_rw_0@64@01 % step@43@01 < N@41@01 | live]
; [else-branch: 3 | !k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01] && k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01] ==> k_fresh_rw_0@64@01 % step@43@01 < N@41@01 | live]
(push) ; 4
; [then-branch: 3 | k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01] && k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01] ==> k_fresh_rw_0@64@01 % step@43@01 < N@41@01]
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
    (< (mod k_fresh_rw_0@64@01 step@43@01) N@41@01))))
; [eval] (matrix[k_fresh_rw_0].Ref__Integer_value in [0..P))
; [eval] [0..P)
; [eval] matrix[k_fresh_rw_0]
(push) ; 5
(assert (not (>= k_fresh_rw_0@64@01 0)))
 (set-option :rlimit 85715) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(push) ; 5
(assert (not (< k_fresh_rw_0@64@01 ($Seq.length matrix@45@01))))
 (set-option :rlimit 31104) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(push) ; 5
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@42@01 step@43@01))
          (inv@63@01 ($Seq.index matrix@45@01 k_fresh_rw_0@64@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@42@01 step@43@01))
            (inv@63@01 ($Seq.index matrix@45@01 k_fresh_rw_0@64@01)))
          (<
            (mod
              (inv@63@01 ($Seq.index matrix@45@01 k_fresh_rw_0@64@01))
              step@43@01)
            N@41@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)
    (ite
      ($Seq.contains
        ($Seq.range 0 P@46@01)
        (inv@57@01 ($Seq.index matrix@45@01 k_fresh_rw_0@64@01)))
      $Perm.Write
      $Perm.No)))))
 (set-option :rlimit 26791) (check-sat) 
; unsat
(pop) ; 5
; 0.01s
; 
(declare-const sm@66@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
          (< (mod (inv@63@01 r) step@43@01) N@41@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
    :qid |qp.fvfValDef1|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
          (< (mod (inv@63@01 r) step@43@01) N@41@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@60@01 r))
    :qid |qp.fvfValDef1|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
    :qid |qp.fvfValDef2|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@54@01 r))
    :qid |qp.fvfValDef2|))))
(pop) ; 4
(push) ; 4
; [else-branch: 3 | !k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01] && k_fresh_rw_0@64@01 in [0..M@42@01 * step@43@01] ==> k_fresh_rw_0@64@01 % step@43@01 < N@41@01]
(assert (not
  (and
    ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
      (< (mod k_fresh_rw_0@64@01 step@43@01) N@41@01)))))
(pop) ; 4
(pop) ; 3
; Joined path conditions
(assert (implies
  (and
    ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
      (< (mod k_fresh_rw_0@64@01 step@43@01) N@41@01)))
  (and
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
        :qid |qp.fvfValDef2|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@54@01 r))
        :qid |qp.fvfValDef2|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (< (mod (inv@63@01 r) step@43@01) N@41@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
        :qid |qp.fvfValDef1|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (< (mod (inv@63@01 r) step@43@01) N@41@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@60@01 r))
        :qid |qp.fvfValDef1|)))
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
        (< (mod k_fresh_rw_0@64@01 step@43@01) N@41@01))))))
; Joined path conditions
(declare-const fvf@67@01 $FVF<Int>)
(pop) ; 2
; Nested auxiliary terms
(assert (forall ((k_fresh_rw_0@64@01 Int) (fvf@67@01 $FVF<Int>)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
        (< (mod k_fresh_rw_0@64@01 step@43@01) N@41@01)))
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
          :qid |qp.fvfValDef2|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@54@01 r))
          :qid |qp.fvfValDef2|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@63@01 r))
                (< (mod (inv@63@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
          :qid |qp.fvfValDef1|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@63@01 r))
                (< (mod (inv@63@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@60@01 r))
          :qid |qp.fvfValDef1|)))
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@42@01 step@43@01))
            k_fresh_rw_0@64@01)
          (< (mod k_fresh_rw_0@64@01 step@43@01) N@41@01)))))
  :pattern (($Seq.contains
    ($Seq.range 0 P@46@01)
    ($FVF.lookup_Ref__Integer_value fvf@67@01 ($Seq.index
      matrix@45@01
      k_fresh_rw_0@64@01))))
  :qid |prog.l83-aux|)))
(assert (forall ((k_fresh_rw_0@64@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@64@01)
        (< (mod k_fresh_rw_0@64@01 step@43@01) N@41@01)))
    ($Seq.contains
      ($Seq.range 0 P@46@01)
      ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) ($Seq.index
        matrix@45@01
        k_fresh_rw_0@64@01))))
  :pattern (($Seq.contains
    ($Seq.range 0 P@46@01)
    ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) ($Seq.index
      matrix@45@01
      k_fresh_rw_0@64@01))))
  :qid |prog.l83|)))
; State saturation: after contract
;(set-option :timeout 50)
 (set-option :rlimit 6621) (check-sat) 
; unknown
(push) ; 2
(declare-const $t@68@01 $Snap)
(declare-const $t@69@01 $Snap)
(assert (= $t@68@01 ($Snap.combine $Snap.unit $t@69@01)))
; [eval] M > 0
(declare-const $t@70@01 $Snap)
(assert (= $t@69@01 ($Snap.combine $Snap.unit $t@70@01)))
; [eval] N > 0
(declare-const $t@71@01 $Snap)
(assert (= $t@70@01 ($Snap.combine $Snap.unit $t@71@01)))
; [eval] step >= N
(declare-const $t@72@01 $Snap)
(assert (= $t@71@01 ($Snap.combine $Snap.unit $t@72@01)))
; [eval] P > 0
(declare-const $t@73@01 $Snap)
(assert (= $t@72@01 ($Snap.combine $Snap.unit $t@73@01)))
; [eval] N <= step
(declare-const $t@74@01 $FVF<Int>)
(declare-const $t@75@01 $Snap)
(assert (= $t@73@01 ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@74@01) $t@75@01)))
(declare-const j@76@01 Int)
(push) ; 3
; [eval] (j in [0..M * step)) && j % step < N
; [eval] (j in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@77@01 ==> j % step < N
(push) ; 4
; [then-branch: 4 | j@76@01 in [0..M@42@01 * step@43@01] | live]
; [else-branch: 4 | !j@76@01 in [0..M@42@01 * step@43@01] | live]
(push) ; 5
; [then-branch: 4 | j@76@01 in [0..M@42@01 * step@43@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@76@01))
; [eval] j % step < N
; [eval] j % step
;(set-option :timeout 0)
(push) ; 6
(assert (not (not (= step@43@01 0))))
 (set-option :rlimit 19280) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(pop) ; 5
(push) ; 5
; [else-branch: 4 | !j@76@01 in [0..M@42@01 * step@43@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@76@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@76@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@76@01)
    (< (mod j@76@01 step@43@01) N@41@01))))
; [eval] matrix[j]
(push) ; 4
(assert (not (>= j@76@01 0)))
 (set-option :rlimit 2708) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< j@76@01 ($Seq.length matrix@45@01))))
 (set-option :rlimit 56191) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (not (= 4 0))))
 (set-option :rlimit 51662) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@78@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((j@76@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@76@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@76@01)
        (< (mod j@76@01 step@43@01) N@41@01)))
    (= (inv@78@01 ($Seq.index matrix@45@01 j@76@01)) j@76@01))
  :pattern (($Seq.index matrix@45@01 j@76@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
        (< (mod (inv@78@01 r) step@43@01) N@41@01)))
    (= ($Seq.index matrix@45@01 (inv@78@01 r)) r))
  :pattern ((inv@78@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j@76@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@76@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) j@76@01)
        (< (mod j@76@01 step@43@01) N@41@01)))
    (not (= ($Seq.index matrix@45@01 j@76@01) $Ref.null)))
  :pattern (($Seq.index matrix@45@01 j@76@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
(declare-const $t@79@01 $FVF<Int>)
(assert (= $t@75@01 ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@79@01) $Snap.unit)))
(declare-const k@80@01 Int)
(push) ; 3
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@46@01) k@80@01))
; [eval] hist[k]
(push) ; 4
(assert (not (>= k@80@01 0)))
 (set-option :rlimit 2737) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< k@80@01 ($Seq.length hist@44@01))))
 (set-option :rlimit 23181) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@81@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((k@80@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@46@01) k@80@01)
    (= (inv@81@01 ($Seq.index hist@44@01 k@80@01)) k@80@01))
  :pattern (($Seq.index hist@44@01 k@80@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
    (= ($Seq.index hist@44@01 (inv@81@01 r)) r))
  :pattern ((inv@81@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((k@80@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@46@01) k@80@01)
    (not (= ($Seq.index hist@44@01 k@80@01) $Ref.null)))
  :pattern (($Seq.index hist@44@01 k@80@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
; [eval] (forall k: Int :: { (k in [0..P)) } { hist[k] } (k in [0..P)) ==> hist[k].Ref__Integer_value == old(hist[k].Ref__Integer_value) + count_square(0, 0, N, step, 0, M * step, matrix, k))
(declare-const k@82@01 Int)
(push) ; 3
; [eval] (k in [0..P)) ==> hist[k].Ref__Integer_value == old(hist[k].Ref__Integer_value) + count_square(0, 0, N, step, 0, M * step, matrix, k)
; [eval] (k in [0..P))
; [eval] [0..P)
(push) ; 4
; [then-branch: 5 | k@82@01 in [0..P@46@01] | live]
; [else-branch: 5 | !k@82@01 in [0..P@46@01] | live]
(push) ; 5
; [then-branch: 5 | k@82@01 in [0..P@46@01]]
(assert ($Seq.contains ($Seq.range 0 P@46@01) k@82@01))
; [eval] hist[k].Ref__Integer_value == old(hist[k].Ref__Integer_value) + count_square(0, 0, N, step, 0, M * step, matrix, k)
; [eval] hist[k]
(push) ; 6
(assert (not (>= k@82@01 0)))
 (set-option :rlimit 13257) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k@82@01 ($Seq.length hist@44@01))))
 (set-option :rlimit 124716) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@46@01)
        (inv@81@01 ($Seq.index hist@44@01 k@82@01)))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@42@01 step@43@01))
          (inv@78@01 ($Seq.index hist@44@01 k@82@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@42@01 step@43@01))
            (inv@78@01 ($Seq.index hist@44@01 k@82@01)))
          (<
            (mod (inv@78@01 ($Seq.index hist@44@01 k@82@01)) step@43@01)
            N@41@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)))))
 (set-option :rlimit 57940) (check-sat) 
; unsat
(pop) ; 6
; 0.01s
; 
(declare-const sm@83@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
    :qid |qp.fvfValDef3|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
    :qid |qp.fvfValDef3|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
          (< (mod (inv@78@01 r) step@43@01) N@41@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
    :qid |qp.fvfValDef4|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
          (< (mod (inv@78@01 r) step@43@01) N@41@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
    :qid |qp.fvfValDef4|))))
; [eval] old(hist[k].Ref__Integer_value) + count_square(0, 0, N, step, 0, M * step, matrix, k)
; [eval] old(hist[k].Ref__Integer_value)
; [eval] hist[k]
(push) ; 6
(assert (not (>= k@82@01 0)))
 (set-option :rlimit 34108) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k@82@01 ($Seq.length hist@44@01))))
 (set-option :rlimit 55624) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@42@01 step@43@01))
          (inv@63@01 ($Seq.index hist@44@01 k@82@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@42@01 step@43@01))
            (inv@63@01 ($Seq.index hist@44@01 k@82@01)))
          (<
            (mod (inv@63@01 ($Seq.index hist@44@01 k@82@01)) step@43@01)
            N@41@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)
    (ite
      ($Seq.contains
        ($Seq.range 0 P@46@01)
        (inv@57@01 ($Seq.index hist@44@01 k@82@01)))
      $Perm.Write
      $Perm.No)))))
 (set-option :rlimit 12029) (check-sat) 
; unsat
(pop) ; 6
; 0.01s
; 
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
          (< (mod (inv@63@01 r) step@43@01) N@41@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
    :qid |qp.fvfValDef1|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
          (< (mod (inv@63@01 r) step@43@01) N@41@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@60@01 r))
    :qid |qp.fvfValDef1|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
    :qid |qp.fvfValDef2|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@54@01 r))
    :qid |qp.fvfValDef2|))))
; [eval] count_square(0, 0, N, step, 0, M * step, matrix, k)
; [eval] M * step
(push) ; 6
; [eval] 0 <= 0
; [eval] 0 <= N
(push) ; 7
(assert (not (<= 0 N@41@01)))
 (set-option :rlimit 5403) (check-sat) 
; unsat
(pop) ; 7
; 0.00s
; 
(assert (<= 0 N@41@01))
; [eval] N <= step
; [eval] step > 0
(push) ; 7
(assert (not (> step@43@01 0)))
 (set-option :rlimit 33432) (check-sat) 
; unsat
(pop) ; 7
; 0.00s
; 
(assert (> step@43@01 0))
; [eval] 0 <= 0
; [eval] 0 <= 0
; [eval] 0 <= M * step
; [eval] M * step
(push) ; 7
(assert (not (<= 0 (* M@42@01 step@43@01))))
 (set-option :rlimit 35651) (check-sat) 
; unsat
(pop) ; 7
; 0.01s
; 
(assert (<= 0 (* M@42@01 step@43@01)))
; [eval] M * step <= |matrix|
; [eval] M * step
; [eval] |matrix|
(declare-const k@84@01 Int)
(push) ; 7
; [eval] 0 <= k && (k < M * step && (0 <= k % step && k % step < N))
; [eval] 0 <= k
; [eval] v@85@01 ==> k < M * step && (0 <= k % step && k % step < N)
(push) ; 8
; [then-branch: 6 | 0 <= k@84@01 | live]
; [else-branch: 6 | !0 <= k@84@01 | live]
(push) ; 9
; [then-branch: 6 | 0 <= k@84@01]
(assert (<= 0 k@84@01))
; [eval] k < M * step && (0 <= k % step && k % step < N)
; [eval] k < M * step
; [eval] M * step
; [eval] v@86@01 ==> 0 <= k % step && k % step < N
(push) ; 10
; [then-branch: 7 | k@84@01 < M@42@01 * step@43@01 | live]
; [else-branch: 7 | !k@84@01 < M@42@01 * step@43@01 | live]
(push) ; 11
; [then-branch: 7 | k@84@01 < M@42@01 * step@43@01]
(assert (< k@84@01 (* M@42@01 step@43@01)))
; [eval] 0 <= k % step && k % step < N
; [eval] 0 <= k % step
; [eval] k % step
(push) ; 12
(assert (not (not (= step@43@01 0))))
 (set-option :rlimit 96191) (check-sat) 
; unsat
(pop) ; 12
; 0.00s
; 
; [eval] v@87@01 ==> k % step < N
(push) ; 12
; [then-branch: 8 | 0 <= k@84@01 % step@43@01 | live]
; [else-branch: 8 | !0 <= k@84@01 % step@43@01 | live]
(push) ; 13
; [then-branch: 8 | 0 <= k@84@01 % step@43@01]
(assert (<= 0 (mod k@84@01 step@43@01)))
; [eval] k % step < N
; [eval] k % step
(push) ; 14
(assert (not (not (= step@43@01 0))))
 (set-option :rlimit 27475) (check-sat) 
; unsat
(pop) ; 14
; 0.00s
; 
(pop) ; 13
(push) ; 13
; [else-branch: 8 | !0 <= k@84@01 % step@43@01]
(assert (not (<= 0 (mod k@84@01 step@43@01))))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
(pop) ; 11
(push) ; 11
; [else-branch: 7 | !k@84@01 < M@42@01 * step@43@01]
(assert (not (< k@84@01 (* M@42@01 step@43@01))))
(pop) ; 11
(pop) ; 10
; Joined path conditions
; Joined path conditions
(pop) ; 9
(push) ; 9
; [else-branch: 6 | !0 <= k@84@01]
(assert (not (<= 0 k@84@01)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (and
  (<= 0 k@84@01)
  (implies
    (<= 0 k@84@01)
    (and
      (< k@84@01 (* M@42@01 step@43@01))
      (implies
        (< k@84@01 (* M@42@01 step@43@01))
        (and
          (<= 0 (mod k@84@01 step@43@01))
          (implies
            (<= 0 (mod k@84@01 step@43@01))
            (< (mod k@84@01 step@43@01) N@41@01))))))))
(declare-const $k@88@01 $Perm)
(assert ($Perm.isReadVar $k@88@01 $Perm.Write))
; [eval] matrix[k]
(push) ; 8
(assert (not (>= k@84@01 0)))
 (set-option :rlimit 110134) (check-sat) 
; unsat
(pop) ; 8
; 0.00s
; 
(push) ; 8
(assert (not (< k@84@01 ($Seq.length matrix@45@01))))
 (set-option :rlimit 169609) (check-sat) 
; unsat
(pop) ; 8
; 0.00s
; 
(pop) ; 7
(declare-fun inv@89@01 ($Ref) Int)
; Nested auxiliary terms
(assert (forall ((k@84@01 Int)) (!
  ($Perm.isReadVar $k@88@01 $Perm.Write)
  :pattern (($Seq.index matrix@45@01 k@84@01))
  :qid |Ref__Integer_value-aux|)))
(push) ; 7
(assert (not (forall ((k@84@01 Int)) (!
  (implies
    (and
      (<= 0 k@84@01)
      (implies
        (<= 0 k@84@01)
        (and
          (< k@84@01 (* M@42@01 step@43@01))
          (implies
            (< k@84@01 (* M@42@01 step@43@01))
            (and
              (<= 0 (mod k@84@01 step@43@01))
              (implies
                (<= 0 (mod k@84@01 step@43@01))
                (< (mod k@84@01 step@43@01) N@41@01)))))))
    (or (= $k@88@01 $Perm.No) (< $Perm.No $k@88@01)))
  
  ))))
 (set-option :rlimit 11547) (check-sat) 
; unsat
(pop) ; 7
; 0.00s
; 
; Check receiver injectivity
(push) ; 7
(assert (not (forall ((k1@84@01 Int) (k2@84@01 Int)) (!
  (implies
    (and
      (and
        (and
          (<= 0 k1@84@01)
          (implies
            (<= 0 k1@84@01)
            (and
              (< k1@84@01 (* M@42@01 step@43@01))
              (implies
                (< k1@84@01 (* M@42@01 step@43@01))
                (and
                  (<= 0 (mod k1@84@01 step@43@01))
                  (implies
                    (<= 0 (mod k1@84@01 step@43@01))
                    (< (mod k1@84@01 step@43@01) N@41@01)))))))
        (< $Perm.No $k@88@01))
      (and
        (and
          (<= 0 k2@84@01)
          (implies
            (<= 0 k2@84@01)
            (and
              (< k2@84@01 (* M@42@01 step@43@01))
              (implies
                (< k2@84@01 (* M@42@01 step@43@01))
                (and
                  (<= 0 (mod k2@84@01 step@43@01))
                  (implies
                    (<= 0 (mod k2@84@01 step@43@01))
                    (< (mod k2@84@01 step@43@01) N@41@01)))))))
        (< $Perm.No $k@88@01))
      (= ($Seq.index matrix@45@01 k1@84@01) ($Seq.index matrix@45@01 k2@84@01)))
    (= k1@84@01 k2@84@01))
  
  :qid |Ref__Integer_value-rcvrInj|))))
 (set-option :rlimit 311) (check-sat) 
; unsat
(pop) ; 7
; 0.02s
; 
; Definitional axioms for inverse functions
(assert (forall ((k@84@01 Int)) (!
  (implies
    (and
      (and
        (<= 0 k@84@01)
        (implies
          (<= 0 k@84@01)
          (and
            (< k@84@01 (* M@42@01 step@43@01))
            (implies
              (< k@84@01 (* M@42@01 step@43@01))
              (and
                (<= 0 (mod k@84@01 step@43@01))
                (implies
                  (<= 0 (mod k@84@01 step@43@01))
                  (< (mod k@84@01 step@43@01) N@41@01)))))))
      (< $Perm.No $k@88@01))
    (= (inv@89@01 ($Seq.index matrix@45@01 k@84@01)) k@84@01))
  :pattern (($Seq.index matrix@45@01 k@84@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    (and
      (and
        (<= 0 (inv@89@01 r))
        (implies
          (<= 0 (inv@89@01 r))
          (and
            (< (inv@89@01 r) (* M@42@01 step@43@01))
            (implies
              (< (inv@89@01 r) (* M@42@01 step@43@01))
              (and
                (<= 0 (mod (inv@89@01 r) step@43@01))
                (implies
                  (<= 0 (mod (inv@89@01 r) step@43@01))
                  (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
      (< $Perm.No $k@88@01))
    (= ($Seq.index matrix@45@01 (inv@89@01 r)) r))
  :pattern ((inv@89@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@90@01 ((r $Ref)) $Perm
  (ite
    (and
      (<= 0 (inv@89@01 r))
      (implies
        (<= 0 (inv@89@01 r))
        (and
          (< (inv@89@01 r) (* M@42@01 step@43@01))
          (implies
            (< (inv@89@01 r) (* M@42@01 step@43@01))
            (and
              (<= 0 (mod (inv@89@01 r) step@43@01))
              (implies
                (<= 0 (mod (inv@89@01 r) step@43@01))
                (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
    ($Perm.min
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
          (implies
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (< (mod (inv@78@01 r) step@43@01) N@41@01)))
        (/ (to_real 1) (to_real 4))
        $Perm.No)
      $k@88@01)
    $Perm.No))
(define-fun pTaken@91@01 ((r $Ref)) $Perm
  (ite
    (and
      (<= 0 (inv@89@01 r))
      (implies
        (<= 0 (inv@89@01 r))
        (and
          (< (inv@89@01 r) (* M@42@01 step@43@01))
          (implies
            (< (inv@89@01 r) (* M@42@01 step@43@01))
            (and
              (<= 0 (mod (inv@89@01 r) step@43@01))
              (implies
                (<= 0 (mod (inv@89@01 r) step@43@01))
                (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
    ($Perm.min
      (ite
        ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
        $Perm.Write
        $Perm.No)
      (- $k@88@01 (pTaken@90@01 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
;(set-option :timeout 10)
 (set-option :rlimit 8729) (check-sat) 
; unknown
; Constrain original permissions $k@88@01
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (not
        (=
          (ite
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (< (mod (inv@78@01 r) step@43@01) N@41@01)))
            (/ (to_real 1) (to_real 4))
            $Perm.No)
          $Perm.No))
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
          (implies
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (< (mod (inv@78@01 r) step@43@01) N@41@01)))
        (<
          (ite
            (and
              (<= 0 (inv@89@01 r))
              (implies
                (<= 0 (inv@89@01 r))
                (and
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (implies
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (and
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (implies
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
            $k@88@01
            $Perm.No)
          (/ (to_real 1) (to_real 4)))
        (<
          (ite
            (and
              (<= 0 (inv@89@01 r))
              (implies
                (<= 0 (inv@89@01 r))
                (and
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (implies
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (and
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (implies
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
            $k@88@01
            $Perm.No)
          $Perm.No)))
    :pattern ((inv@78@01 r))
    :qid |qp.srp5|))
  (forall ((r $Ref)) (!
    (implies
      (not
        (=
          (ite
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (< (mod (inv@78@01 r) step@43@01) N@41@01)))
            (/ (to_real 1) (to_real 4))
            $Perm.No)
          $Perm.No))
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
          (implies
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (< (mod (inv@78@01 r) step@43@01) N@41@01)))
        (<
          (ite
            (and
              (<= 0 (inv@89@01 r))
              (implies
                (<= 0 (inv@89@01 r))
                (and
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (implies
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (and
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (implies
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
            $k@88@01
            $Perm.No)
          (/ (to_real 1) (to_real 4)))
        (<
          (ite
            (and
              (<= 0 (inv@89@01 r))
              (implies
                (<= 0 (inv@89@01 r))
                (and
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (implies
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (and
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (implies
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
            $k@88@01
            $Perm.No)
          $Perm.No)))
    :pattern ((inv@89@01 r))
    :qid |qp.srp5|))))
; Intermediate check if already taken enough permissions
;(set-option :timeout 500)
(push) ; 7
(assert (not (forall ((r $Ref)) (!
  (implies
    (and
      (<= 0 (inv@89@01 r))
      (implies
        (<= 0 (inv@89@01 r))
        (and
          (< (inv@89@01 r) (* M@42@01 step@43@01))
          (implies
            (< (inv@89@01 r) (* M@42@01 step@43@01))
            (and
              (<= 0 (mod (inv@89@01 r) step@43@01))
              (implies
                (<= 0 (mod (inv@89@01 r) step@43@01))
                (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
    (= (- $k@88@01 (pTaken@90@01 r)) $Perm.No))
  
  ))))
 (set-option :rlimit 59189) (check-sat) 
; unsat
(pop) ; 7
; 0.03s
; 
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@92@01 $FVF<Int>)
; Definitional axioms for SM domain
(assert (forall ((r $Ref)) (!
  (iff
    (Set_in r ($FVF.domain_Ref__Integer_value (as sm@92@01  $FVF<Int>)))
    (and
      (and
        (<= 0 (inv@89@01 r))
        (implies
          (<= 0 (inv@89@01 r))
          (and
            (< (inv@89@01 r) (* M@42@01 step@43@01))
            (implies
              (< (inv@89@01 r) (* M@42@01 step@43@01))
              (and
                (<= 0 (mod (inv@89@01 r) step@43@01))
                (implies
                  (<= 0 (mod (inv@89@01 r) step@43@01))
                  (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
      (< $Perm.No $k@88@01)))
  :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@92@01  $FVF<Int>))))
  :qid |qp.fvfDomDef8|)))
; Definitional axioms for SM values
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@89@01 r))
            (implies
              (<= 0 (inv@89@01 r))
              (and
                (< (inv@89@01 r) (* M@42@01 step@43@01))
                (implies
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (and
                    (<= 0 (mod (inv@89@01 r) step@43@01))
                    (implies
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
          (< $Perm.No $k@88@01))
        ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r))
    :qid |qp.fvfValDef6|))
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@89@01 r))
            (implies
              (<= 0 (inv@89@01 r))
              (and
                (< (inv@89@01 r) (* M@42@01 step@43@01))
                (implies
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (and
                    (<= 0 (mod (inv@89@01 r) step@43@01))
                    (implies
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
          (< $Perm.No $k@88@01))
        ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
    :qid |qp.fvfValDef6|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@89@01 r))
            (implies
              (<= 0 (inv@89@01 r))
              (and
                (< (inv@89@01 r) (* M@42@01 step@43@01))
                (implies
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (and
                    (<= 0 (mod (inv@89@01 r) step@43@01))
                    (implies
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
          (< $Perm.No $k@88@01))
        (and
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
          (implies
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (< (mod (inv@78@01 r) step@43@01) N@41@01))))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r))
    :qid |qp.fvfValDef7|))
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@89@01 r))
            (implies
              (<= 0 (inv@89@01 r))
              (and
                (< (inv@89@01 r) (* M@42@01 step@43@01))
                (implies
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (and
                    (<= 0 (mod (inv@89@01 r) step@43@01))
                    (implies
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
          (< $Perm.No $k@88@01))
        (and
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
          (implies
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (< (mod (inv@78@01 r) step@43@01) N@41@01))))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
    :qid |qp.fvfValDef7|))))
(pop) ; 6
; Joined path conditions
(assert (and
  (and
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@89@01 r))
              (implies
                (<= 0 (inv@89@01 r))
                (and
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (implies
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (and
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (implies
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
            (< $Perm.No $k@88@01))
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (< (mod (inv@78@01 r) step@43@01) N@41@01))))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r))
      :qid |qp.fvfValDef7|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@89@01 r))
              (implies
                (<= 0 (inv@89@01 r))
                (and
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (implies
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (and
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (implies
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
            (< $Perm.No $k@88@01))
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (< (mod (inv@78@01 r) step@43@01) N@41@01))))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
      :qid |qp.fvfValDef7|)))
  (and
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@89@01 r))
              (implies
                (<= 0 (inv@89@01 r))
                (and
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (implies
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (and
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (implies
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
            (< $Perm.No $k@88@01))
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r)))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r))
      :qid |qp.fvfValDef6|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@89@01 r))
              (implies
                (<= 0 (inv@89@01 r))
                (and
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (implies
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (and
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (implies
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
            (< $Perm.No $k@88@01))
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r)))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
      :qid |qp.fvfValDef6|)))
  (forall ((r $Ref)) (!
    (iff
      (Set_in r ($FVF.domain_Ref__Integer_value (as sm@92@01  $FVF<Int>)))
      (and
        (and
          (<= 0 (inv@89@01 r))
          (implies
            (<= 0 (inv@89@01 r))
            (and
              (< (inv@89@01 r) (* M@42@01 step@43@01))
              (implies
                (< (inv@89@01 r) (* M@42@01 step@43@01))
                (and
                  (<= 0 (mod (inv@89@01 r) step@43@01))
                  (implies
                    (<= 0 (mod (inv@89@01 r) step@43@01))
                    (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
        (< $Perm.No $k@88@01)))
    :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@92@01  $FVF<Int>))))
    :qid |qp.fvfDomDef8|))
  (and
    (forall ((r $Ref)) (!
      (implies
        (not
          (=
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (< (mod (inv@78@01 r) step@43@01) N@41@01)))
              (/ (to_real 1) (to_real 4))
              $Perm.No)
            $Perm.No))
        (ite
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (< (mod (inv@78@01 r) step@43@01) N@41@01)))
          (<
            (ite
              (and
                (<= 0 (inv@89@01 r))
                (implies
                  (<= 0 (inv@89@01 r))
                  (and
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (implies
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (and
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (implies
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
              $k@88@01
              $Perm.No)
            (/ (to_real 1) (to_real 4)))
          (<
            (ite
              (and
                (<= 0 (inv@89@01 r))
                (implies
                  (<= 0 (inv@89@01 r))
                  (and
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (implies
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (and
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (implies
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
              $k@88@01
              $Perm.No)
            $Perm.No)))
      :pattern ((inv@78@01 r))
      :qid |qp.srp5|))
    (forall ((r $Ref)) (!
      (implies
        (not
          (=
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (< (mod (inv@78@01 r) step@43@01) N@41@01)))
              (/ (to_real 1) (to_real 4))
              $Perm.No)
            $Perm.No))
        (ite
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (< (mod (inv@78@01 r) step@43@01) N@41@01)))
          (<
            (ite
              (and
                (<= 0 (inv@89@01 r))
                (implies
                  (<= 0 (inv@89@01 r))
                  (and
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (implies
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (and
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (implies
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
              $k@88@01
              $Perm.No)
            (/ (to_real 1) (to_real 4)))
          (<
            (ite
              (and
                (<= 0 (inv@89@01 r))
                (implies
                  (<= 0 (inv@89@01 r))
                  (and
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (implies
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (and
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (implies
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
              $k@88@01
              $Perm.No)
            $Perm.No)))
      :pattern ((inv@89@01 r))
      :qid |qp.srp5|)))
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (<= 0 (inv@89@01 r))
          (implies
            (<= 0 (inv@89@01 r))
            (and
              (< (inv@89@01 r) (* M@42@01 step@43@01))
              (implies
                (< (inv@89@01 r) (* M@42@01 step@43@01))
                (and
                  (<= 0 (mod (inv@89@01 r) step@43@01))
                  (implies
                    (<= 0 (mod (inv@89@01 r) step@43@01))
                    (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
        (< $Perm.No $k@88@01))
      (= ($Seq.index matrix@45@01 (inv@89@01 r)) r))
    :pattern ((inv@89@01 r))
    :qid |Ref__Integer_value-fctOfInv|))
  (forall ((k@84@01 Int)) (!
    (implies
      (and
        (and
          (<= 0 k@84@01)
          (implies
            (<= 0 k@84@01)
            (and
              (< k@84@01 (* M@42@01 step@43@01))
              (implies
                (< k@84@01 (* M@42@01 step@43@01))
                (and
                  (<= 0 (mod k@84@01 step@43@01))
                  (implies
                    (<= 0 (mod k@84@01 step@43@01))
                    (< (mod k@84@01 step@43@01) N@41@01)))))))
        (< $Perm.No $k@88@01))
      (= (inv@89@01 ($Seq.index matrix@45@01 k@84@01)) k@84@01))
    :pattern (($Seq.index matrix@45@01 k@84@01))
    :qid |Ref__Integer_value-invOfFct|))
  (forall ((k@84@01 Int)) (!
    ($Perm.isReadVar $k@88@01 $Perm.Write)
    :pattern (($Seq.index matrix@45@01 k@84@01))
    :qid |Ref__Integer_value-aux|))
  (<= 0 (* M@42@01 step@43@01))
  (> step@43@01 0)
  (<= 0 N@41@01)))
(pop) ; 5
(push) ; 5
; [else-branch: 5 | !k@82@01 in [0..P@46@01]]
(assert (not ($Seq.contains ($Seq.range 0 P@46@01) k@82@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (implies
  ($Seq.contains ($Seq.range 0 P@46@01) k@82@01)
  (and
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@89@01 r))
                  (implies
                    (<= 0 (inv@89@01 r))
                    (and
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (implies
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (and
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (implies
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                (< $Perm.No $k@88@01))
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (< (mod (inv@78@01 r) step@43@01) N@41@01))))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r))
          :qid |qp.fvfValDef7|))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@89@01 r))
                  (implies
                    (<= 0 (inv@89@01 r))
                    (and
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (implies
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (and
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (implies
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                (< $Perm.No $k@88@01))
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (< (mod (inv@78@01 r) step@43@01) N@41@01))))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
          :qid |qp.fvfValDef7|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@89@01 r))
                  (implies
                    (<= 0 (inv@89@01 r))
                    (and
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (implies
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (and
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (implies
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                (< $Perm.No $k@88@01))
              ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r))
          :qid |qp.fvfValDef6|))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@89@01 r))
                  (implies
                    (<= 0 (inv@89@01 r))
                    (and
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (implies
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (and
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (implies
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                (< $Perm.No $k@88@01))
              ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
          :qid |qp.fvfValDef6|)))
      (forall ((r $Ref)) (!
        (iff
          (Set_in r ($FVF.domain_Ref__Integer_value (as sm@92@01  $FVF<Int>)))
          (and
            (and
              (<= 0 (inv@89@01 r))
              (implies
                (<= 0 (inv@89@01 r))
                (and
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (implies
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (and
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (implies
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
            (< $Perm.No $k@88@01)))
        :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@92@01  $FVF<Int>))))
        :qid |qp.fvfDomDef8|))
      (and
        (forall ((r $Ref)) (!
          (implies
            (not
              (=
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@42@01 step@43@01))
                      (inv@78@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@42@01 step@43@01))
                        (inv@78@01 r))
                      (< (mod (inv@78@01 r) step@43@01) N@41@01)))
                  (/ (to_real 1) (to_real 4))
                  $Perm.No)
                $Perm.No))
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (< (mod (inv@78@01 r) step@43@01) N@41@01)))
              (<
                (ite
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  $k@88@01
                  $Perm.No)
                (/ (to_real 1) (to_real 4)))
              (<
                (ite
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  $k@88@01
                  $Perm.No)
                $Perm.No)))
          :pattern ((inv@78@01 r))
          :qid |qp.srp5|))
        (forall ((r $Ref)) (!
          (implies
            (not
              (=
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@42@01 step@43@01))
                      (inv@78@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@42@01 step@43@01))
                        (inv@78@01 r))
                      (< (mod (inv@78@01 r) step@43@01) N@41@01)))
                  (/ (to_real 1) (to_real 4))
                  $Perm.No)
                $Perm.No))
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (< (mod (inv@78@01 r) step@43@01) N@41@01)))
              (<
                (ite
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  $k@88@01
                  $Perm.No)
                (/ (to_real 1) (to_real 4)))
              (<
                (ite
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  $k@88@01
                  $Perm.No)
                $Perm.No)))
          :pattern ((inv@89@01 r))
          :qid |qp.srp5|)))
      (forall ((r $Ref)) (!
        (implies
          (and
            (and
              (<= 0 (inv@89@01 r))
              (implies
                (<= 0 (inv@89@01 r))
                (and
                  (< (inv@89@01 r) (* M@42@01 step@43@01))
                  (implies
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (and
                      (<= 0 (mod (inv@89@01 r) step@43@01))
                      (implies
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
            (< $Perm.No $k@88@01))
          (= ($Seq.index matrix@45@01 (inv@89@01 r)) r))
        :pattern ((inv@89@01 r))
        :qid |Ref__Integer_value-fctOfInv|))
      (forall ((k@84@01 Int)) (!
        (implies
          (and
            (and
              (<= 0 k@84@01)
              (implies
                (<= 0 k@84@01)
                (and
                  (< k@84@01 (* M@42@01 step@43@01))
                  (implies
                    (< k@84@01 (* M@42@01 step@43@01))
                    (and
                      (<= 0 (mod k@84@01 step@43@01))
                      (implies
                        (<= 0 (mod k@84@01 step@43@01))
                        (< (mod k@84@01 step@43@01) N@41@01)))))))
            (< $Perm.No $k@88@01))
          (= (inv@89@01 ($Seq.index matrix@45@01 k@84@01)) k@84@01))
        :pattern (($Seq.index matrix@45@01 k@84@01))
        :qid |Ref__Integer_value-invOfFct|))
      (forall ((k@84@01 Int)) (!
        ($Perm.isReadVar $k@88@01 $Perm.Write)
        :pattern (($Seq.index matrix@45@01 k@84@01))
        :qid |Ref__Integer_value-aux|))
      (<= 0 (* M@42@01 step@43@01))
      (> step@43@01 0)
      (<= 0 N@41@01))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
        :qid |qp.fvfValDef2|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@54@01 r))
        :qid |qp.fvfValDef2|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (< (mod (inv@63@01 r) step@43@01) N@41@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
        :qid |qp.fvfValDef1|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (< (mod (inv@63@01 r) step@43@01) N@41@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@60@01 r))
        :qid |qp.fvfValDef1|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (< (mod (inv@78@01 r) step@43@01) N@41@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
        :qid |qp.fvfValDef4|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (< (mod (inv@78@01 r) step@43@01) N@41@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
        :qid |qp.fvfValDef4|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
        :qid |qp.fvfValDef3|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
        :qid |qp.fvfValDef3|)))
    ($Seq.contains ($Seq.range 0 P@46@01) k@82@01))))
; Joined path conditions
; [eval] hist[k]
;(set-option :timeout 0)
(push) ; 4
(assert (not (>= k@82@01 0)))
 (set-option :rlimit 10559) (check-sat) 
; unknown
(pop) ; 4
; 0.01s
; 
(pop) ; 3
; Nested auxiliary terms
(assert (forall ((k@82@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@46@01) k@82@01)
    (and
      (and
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  (< $Perm.No $k@88@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@42@01 step@43@01))
                      (inv@78@01 r))
                    (< (mod (inv@78@01 r) step@43@01) N@41@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r))
            :qid |qp.fvfValDef7|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  (< $Perm.No $k@88@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@42@01 step@43@01))
                      (inv@78@01 r))
                    (< (mod (inv@78@01 r) step@43@01) N@41@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
            :qid |qp.fvfValDef7|)))
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  (< $Perm.No $k@88@01))
                ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r))
            :qid |qp.fvfValDef6|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  (< $Perm.No $k@88@01))
                ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
            :qid |qp.fvfValDef6|)))
        (forall ((r $Ref)) (!
          (iff
            (Set_in r ($FVF.domain_Ref__Integer_value (as sm@92@01  $FVF<Int>)))
            (and
              (and
                (<= 0 (inv@89@01 r))
                (implies
                  (<= 0 (inv@89@01 r))
                  (and
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (implies
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (and
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (implies
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
              (< $Perm.No $k@88@01)))
          :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@92@01  $FVF<Int>))))
          :qid |qp.fvfDomDef8|))
        (and
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@42@01 step@43@01))
                        (inv@78@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@42@01 step@43@01))
                          (inv@78@01 r))
                        (< (mod (inv@78@01 r) step@43@01) N@41@01)))
                    (/ (to_real 1) (to_real 4))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@42@01 step@43@01))
                      (inv@78@01 r))
                    (< (mod (inv@78@01 r) step@43@01) N@41@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@89@01 r))
                      (implies
                        (<= 0 (inv@89@01 r))
                        (and
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (implies
                            (< (inv@89@01 r) (* M@42@01 step@43@01))
                            (and
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (implies
                                (<= 0 (mod (inv@89@01 r) step@43@01))
                                (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                    $k@88@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 4)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@89@01 r))
                      (implies
                        (<= 0 (inv@89@01 r))
                        (and
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (implies
                            (< (inv@89@01 r) (* M@42@01 step@43@01))
                            (and
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (implies
                                (<= 0 (mod (inv@89@01 r) step@43@01))
                                (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                    $k@88@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@78@01 r))
            :qid |qp.srp5|))
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@42@01 step@43@01))
                        (inv@78@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@42@01 step@43@01))
                          (inv@78@01 r))
                        (< (mod (inv@78@01 r) step@43@01) N@41@01)))
                    (/ (to_real 1) (to_real 4))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@42@01 step@43@01))
                      (inv@78@01 r))
                    (< (mod (inv@78@01 r) step@43@01) N@41@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@89@01 r))
                      (implies
                        (<= 0 (inv@89@01 r))
                        (and
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (implies
                            (< (inv@89@01 r) (* M@42@01 step@43@01))
                            (and
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (implies
                                (<= 0 (mod (inv@89@01 r) step@43@01))
                                (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                    $k@88@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 4)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@89@01 r))
                      (implies
                        (<= 0 (inv@89@01 r))
                        (and
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (implies
                            (< (inv@89@01 r) (* M@42@01 step@43@01))
                            (and
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (implies
                                (<= 0 (mod (inv@89@01 r) step@43@01))
                                (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                    $k@88@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@89@01 r))
            :qid |qp.srp5|)))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (<= 0 (inv@89@01 r))
                (implies
                  (<= 0 (inv@89@01 r))
                  (and
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (implies
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (and
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (implies
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
              (< $Perm.No $k@88@01))
            (= ($Seq.index matrix@45@01 (inv@89@01 r)) r))
          :pattern ((inv@89@01 r))
          :qid |Ref__Integer_value-fctOfInv|))
        (forall ((k@84@01 Int)) (!
          (implies
            (and
              (and
                (<= 0 k@84@01)
                (implies
                  (<= 0 k@84@01)
                  (and
                    (< k@84@01 (* M@42@01 step@43@01))
                    (implies
                      (< k@84@01 (* M@42@01 step@43@01))
                      (and
                        (<= 0 (mod k@84@01 step@43@01))
                        (implies
                          (<= 0 (mod k@84@01 step@43@01))
                          (< (mod k@84@01 step@43@01) N@41@01)))))))
              (< $Perm.No $k@88@01))
            (= (inv@89@01 ($Seq.index matrix@45@01 k@84@01)) k@84@01))
          :pattern (($Seq.index matrix@45@01 k@84@01))
          :qid |Ref__Integer_value-invOfFct|))
        (forall ((k@84@01 Int)) (!
          ($Perm.isReadVar $k@88@01 $Perm.Write)
          :pattern (($Seq.index matrix@45@01 k@84@01))
          :qid |Ref__Integer_value-aux|))
        (<= 0 (* M@42@01 step@43@01))
        (> step@43@01 0)
        (<= 0 N@41@01))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
          :qid |qp.fvfValDef2|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@54@01 r))
          :qid |qp.fvfValDef2|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@63@01 r))
                (< (mod (inv@63@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
          :qid |qp.fvfValDef1|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@63@01 r))
                (< (mod (inv@63@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@60@01 r))
          :qid |qp.fvfValDef1|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (< (mod (inv@78@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
          :qid |qp.fvfValDef4|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (< (mod (inv@78@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
          :qid |qp.fvfValDef4|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
          :qid |qp.fvfValDef3|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
          :qid |qp.fvfValDef3|)))
      ($Seq.contains ($Seq.range 0 P@46@01) k@82@01)))
  :pattern (($Seq.contains ($Seq.range 0 P@46@01) k@82@01))
  :qid |prog.l88-aux|)))
(assert (forall ((k@82@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@46@01) k@82@01)
    (and
      (and
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  (< $Perm.No $k@88@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@42@01 step@43@01))
                      (inv@78@01 r))
                    (< (mod (inv@78@01 r) step@43@01) N@41@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r))
            :qid |qp.fvfValDef7|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  (< $Perm.No $k@88@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@42@01 step@43@01))
                      (inv@78@01 r))
                    (< (mod (inv@78@01 r) step@43@01) N@41@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
            :qid |qp.fvfValDef7|)))
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  (< $Perm.No $k@88@01))
                ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r))
            :qid |qp.fvfValDef6|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@89@01 r))
                    (implies
                      (<= 0 (inv@89@01 r))
                      (and
                        (< (inv@89@01 r) (* M@42@01 step@43@01))
                        (implies
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (and
                            (<= 0 (mod (inv@89@01 r) step@43@01))
                            (implies
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                  (< $Perm.No $k@88@01))
                ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@92@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
            :qid |qp.fvfValDef6|)))
        (forall ((r $Ref)) (!
          (iff
            (Set_in r ($FVF.domain_Ref__Integer_value (as sm@92@01  $FVF<Int>)))
            (and
              (and
                (<= 0 (inv@89@01 r))
                (implies
                  (<= 0 (inv@89@01 r))
                  (and
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (implies
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (and
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (implies
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
              (< $Perm.No $k@88@01)))
          :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@92@01  $FVF<Int>))))
          :qid |qp.fvfDomDef8|))
        (and
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@42@01 step@43@01))
                        (inv@78@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@42@01 step@43@01))
                          (inv@78@01 r))
                        (< (mod (inv@78@01 r) step@43@01) N@41@01)))
                    (/ (to_real 1) (to_real 4))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@42@01 step@43@01))
                      (inv@78@01 r))
                    (< (mod (inv@78@01 r) step@43@01) N@41@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@89@01 r))
                      (implies
                        (<= 0 (inv@89@01 r))
                        (and
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (implies
                            (< (inv@89@01 r) (* M@42@01 step@43@01))
                            (and
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (implies
                                (<= 0 (mod (inv@89@01 r) step@43@01))
                                (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                    $k@88@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 4)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@89@01 r))
                      (implies
                        (<= 0 (inv@89@01 r))
                        (and
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (implies
                            (< (inv@89@01 r) (* M@42@01 step@43@01))
                            (and
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (implies
                                (<= 0 (mod (inv@89@01 r) step@43@01))
                                (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                    $k@88@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@78@01 r))
            :qid |qp.srp5|))
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@42@01 step@43@01))
                        (inv@78@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@42@01 step@43@01))
                          (inv@78@01 r))
                        (< (mod (inv@78@01 r) step@43@01) N@41@01)))
                    (/ (to_real 1) (to_real 4))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@42@01 step@43@01))
                    (inv@78@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@42@01 step@43@01))
                      (inv@78@01 r))
                    (< (mod (inv@78@01 r) step@43@01) N@41@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@89@01 r))
                      (implies
                        (<= 0 (inv@89@01 r))
                        (and
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (implies
                            (< (inv@89@01 r) (* M@42@01 step@43@01))
                            (and
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (implies
                                (<= 0 (mod (inv@89@01 r) step@43@01))
                                (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                    $k@88@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 4)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@89@01 r))
                      (implies
                        (<= 0 (inv@89@01 r))
                        (and
                          (< (inv@89@01 r) (* M@42@01 step@43@01))
                          (implies
                            (< (inv@89@01 r) (* M@42@01 step@43@01))
                            (and
                              (<= 0 (mod (inv@89@01 r) step@43@01))
                              (implies
                                (<= 0 (mod (inv@89@01 r) step@43@01))
                                (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
                    $k@88@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@89@01 r))
            :qid |qp.srp5|)))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (<= 0 (inv@89@01 r))
                (implies
                  (<= 0 (inv@89@01 r))
                  (and
                    (< (inv@89@01 r) (* M@42@01 step@43@01))
                    (implies
                      (< (inv@89@01 r) (* M@42@01 step@43@01))
                      (and
                        (<= 0 (mod (inv@89@01 r) step@43@01))
                        (implies
                          (<= 0 (mod (inv@89@01 r) step@43@01))
                          (< (mod (inv@89@01 r) step@43@01) N@41@01)))))))
              (< $Perm.No $k@88@01))
            (= ($Seq.index matrix@45@01 (inv@89@01 r)) r))
          :pattern ((inv@89@01 r))
          :qid |Ref__Integer_value-fctOfInv|))
        (forall ((k@84@01 Int)) (!
          (implies
            (and
              (and
                (<= 0 k@84@01)
                (implies
                  (<= 0 k@84@01)
                  (and
                    (< k@84@01 (* M@42@01 step@43@01))
                    (implies
                      (< k@84@01 (* M@42@01 step@43@01))
                      (and
                        (<= 0 (mod k@84@01 step@43@01))
                        (implies
                          (<= 0 (mod k@84@01 step@43@01))
                          (< (mod k@84@01 step@43@01) N@41@01)))))))
              (< $Perm.No $k@88@01))
            (= (inv@89@01 ($Seq.index matrix@45@01 k@84@01)) k@84@01))
          :pattern (($Seq.index matrix@45@01 k@84@01))
          :qid |Ref__Integer_value-invOfFct|))
        (forall ((k@84@01 Int)) (!
          ($Perm.isReadVar $k@88@01 $Perm.Write)
          :pattern (($Seq.index matrix@45@01 k@84@01))
          :qid |Ref__Integer_value-aux|))
        (<= 0 (* M@42@01 step@43@01))
        (> step@43@01 0)
        (<= 0 N@41@01))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
          :qid |qp.fvfValDef2|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@54@01 r))
          :qid |qp.fvfValDef2|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@63@01 r))
                (< (mod (inv@63@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
          :qid |qp.fvfValDef1|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@63@01 r))
                (< (mod (inv@63@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@60@01 r))
          :qid |qp.fvfValDef1|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (< (mod (inv@78@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
          :qid |qp.fvfValDef4|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (< (mod (inv@78@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
          :qid |qp.fvfValDef4|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
          :qid |qp.fvfValDef3|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
          :qid |qp.fvfValDef3|)))
      ($Seq.contains ($Seq.range 0 P@46@01) k@82@01)))
  :pattern ()
  :qid |prog.l88-aux|)))
(assert (and
  (forall ((k@82@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) k@82@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) ($Seq.index
          hist@44@01
          k@82@01))
        (+
          ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) ($Seq.index
            hist@44@01
            k@82@01))
          (count_square ($Snap.combine
            $Snap.unit
            ($Snap.combine
              $Snap.unit
              ($Snap.combine
                $Snap.unit
                ($Snap.combine
                  $Snap.unit
                  ($Snap.combine
                    $Snap.unit
                    ($Snap.combine
                      $Snap.unit
                      ($Snap.combine
                        $Snap.unit
                        ($Snap.combine
                          $Snap.unit
                          ($SortWrappers.$FVF<Int>To$Snap (as sm@92@01  $FVF<Int>)))))))))) 0 0 N@41@01 step@43@01 0 (*
            M@42@01
            step@43@01) matrix@45@01 k@82@01))))
    :pattern (($Seq.contains ($Seq.range 0 P@46@01) k@82@01))
    :qid |prog.l88|))
  (forall ((k@82@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) k@82@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) ($Seq.index
          hist@44@01
          k@82@01))
        (+
          ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) ($Seq.index
            hist@44@01
            k@82@01))
          (count_square ($Snap.combine
            $Snap.unit
            ($Snap.combine
              $Snap.unit
              ($Snap.combine
                $Snap.unit
                ($Snap.combine
                  $Snap.unit
                  ($Snap.combine
                    $Snap.unit
                    ($Snap.combine
                      $Snap.unit
                      ($Snap.combine
                        $Snap.unit
                        ($Snap.combine
                          $Snap.unit
                          ($SortWrappers.$FVF<Int>To$Snap (as sm@92@01  $FVF<Int>)))))))))) 0 0 N@41@01 step@43@01 0 (*
            M@42@01
            step@43@01) matrix@45@01 k@82@01))))
    :pattern ()
    :qid |prog.l88|))))
; [eval] N <= step
; [eval] (forall k_fresh_rw_0: Int :: { matrix[k_fresh_rw_0] } (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> matrix[k_fresh_rw_0].Ref__Integer_value == old(matrix[k_fresh_rw_0].Ref__Integer_value))
(declare-const k_fresh_rw_0@93@01 Int)
(push) ; 3
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> matrix[k_fresh_rw_0].Ref__Integer_value == old(matrix[k_fresh_rw_0].Ref__Integer_value)
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N
; [eval] (k_fresh_rw_0 in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@94@01 ==> k_fresh_rw_0 % step < N
(push) ; 4
; [then-branch: 9 | k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01] | live]
; [else-branch: 9 | !k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01] | live]
(push) ; 5
; [then-branch: 9 | k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01))
; [eval] k_fresh_rw_0 % step < N
; [eval] k_fresh_rw_0 % step
(push) ; 6
(assert (not (not (= step@43@01 0))))
 (set-option :rlimit 87912) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(pop) ; 5
(push) ; 5
; [else-branch: 9 | !k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(push) ; 4
; [then-branch: 10 | k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01] && k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01] ==> k_fresh_rw_0@93@01 % step@43@01 < N@41@01 | live]
; [else-branch: 10 | !k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01] && k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01] ==> k_fresh_rw_0@93@01 % step@43@01 < N@41@01 | live]
(push) ; 5
; [then-branch: 10 | k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01] && k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01] ==> k_fresh_rw_0@93@01 % step@43@01 < N@41@01]
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
    (< (mod k_fresh_rw_0@93@01 step@43@01) N@41@01))))
; [eval] matrix[k_fresh_rw_0].Ref__Integer_value == old(matrix[k_fresh_rw_0].Ref__Integer_value)
; [eval] matrix[k_fresh_rw_0]
(push) ; 6
(assert (not (>= k_fresh_rw_0@93@01 0)))
 (set-option :rlimit 14569) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k_fresh_rw_0@93@01 ($Seq.length matrix@45@01))))
 (set-option :rlimit 112724) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@46@01)
        (inv@81@01 ($Seq.index matrix@45@01 k_fresh_rw_0@93@01)))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@42@01 step@43@01))
          (inv@78@01 ($Seq.index matrix@45@01 k_fresh_rw_0@93@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@42@01 step@43@01))
            (inv@78@01 ($Seq.index matrix@45@01 k_fresh_rw_0@93@01)))
          (<
            (mod
              (inv@78@01 ($Seq.index matrix@45@01 k_fresh_rw_0@93@01))
              step@43@01)
            N@41@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)))))
 (set-option :rlimit 131825) (check-sat) 
; unsat
(pop) ; 6
; 0.02s
; 
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
    :qid |qp.fvfValDef3|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
    :qid |qp.fvfValDef3|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
          (< (mod (inv@78@01 r) step@43@01) N@41@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
    :qid |qp.fvfValDef4|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
          (< (mod (inv@78@01 r) step@43@01) N@41@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
    :qid |qp.fvfValDef4|))))
; [eval] old(matrix[k_fresh_rw_0].Ref__Integer_value)
; [eval] matrix[k_fresh_rw_0]
(push) ; 6
(assert (not (>= k_fresh_rw_0@93@01 0)))
 (set-option :rlimit 33139) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k_fresh_rw_0@93@01 ($Seq.length matrix@45@01))))
 (set-option :rlimit 23811) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@42@01 step@43@01))
          (inv@63@01 ($Seq.index matrix@45@01 k_fresh_rw_0@93@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@42@01 step@43@01))
            (inv@63@01 ($Seq.index matrix@45@01 k_fresh_rw_0@93@01)))
          (<
            (mod
              (inv@63@01 ($Seq.index matrix@45@01 k_fresh_rw_0@93@01))
              step@43@01)
            N@41@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)
    (ite
      ($Seq.contains
        ($Seq.range 0 P@46@01)
        (inv@57@01 ($Seq.index matrix@45@01 k_fresh_rw_0@93@01)))
      $Perm.Write
      $Perm.No)))))
 (set-option :rlimit 7340) (check-sat) 
; unsat
(pop) ; 6
; 0.02s
; 
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
          (< (mod (inv@63@01 r) step@43@01) N@41@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
    :qid |qp.fvfValDef1|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
          (< (mod (inv@63@01 r) step@43@01) N@41@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@60@01 r))
    :qid |qp.fvfValDef1|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
    :qid |qp.fvfValDef2|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@54@01 r))
    :qid |qp.fvfValDef2|))))
(pop) ; 5
(push) ; 5
; [else-branch: 10 | !k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01] && k_fresh_rw_0@93@01 in [0..M@42@01 * step@43@01] ==> k_fresh_rw_0@93@01 % step@43@01 < N@41@01]
(assert (not
  (and
    ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
      (< (mod k_fresh_rw_0@93@01 step@43@01) N@41@01)))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (implies
  (and
    ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
      (< (mod k_fresh_rw_0@93@01 step@43@01) N@41@01)))
  (and
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
        :qid |qp.fvfValDef2|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@54@01 r))
        :qid |qp.fvfValDef2|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (< (mod (inv@63@01 r) step@43@01) N@41@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
        :qid |qp.fvfValDef1|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (< (mod (inv@63@01 r) step@43@01) N@41@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@60@01 r))
        :qid |qp.fvfValDef1|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (< (mod (inv@78@01 r) step@43@01) N@41@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
        :qid |qp.fvfValDef4|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
            (implies
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (< (mod (inv@78@01 r) step@43@01) N@41@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
        :qid |qp.fvfValDef4|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
        :qid |qp.fvfValDef3|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
        :qid |qp.fvfValDef3|)))
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
        (< (mod k_fresh_rw_0@93@01 step@43@01) N@41@01))))))
; Joined path conditions
(pop) ; 3
; Nested auxiliary terms
(assert (forall ((k_fresh_rw_0@93@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
        (< (mod k_fresh_rw_0@93@01 step@43@01) N@41@01)))
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
          :qid |qp.fvfValDef2|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@57@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@54@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@54@01 r))
          :qid |qp.fvfValDef2|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@63@01 r))
                (< (mod (inv@63@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r))
          :qid |qp.fvfValDef1|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@63@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@63@01 r))
                (< (mod (inv@63@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@60@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@60@01 r))
          :qid |qp.fvfValDef1|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (< (mod (inv@78@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
          :qid |qp.fvfValDef4|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) (inv@78@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@42@01 step@43@01))
                  (inv@78@01 r))
                (< (mod (inv@78@01 r) step@43@01) N@41@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@74@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@74@01 r))
          :qid |qp.fvfValDef4|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r))
          :qid |qp.fvfValDef3|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@46@01) (inv@81@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@79@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@79@01 r))
          :qid |qp.fvfValDef3|)))
      (and
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@42@01 step@43@01))
            k_fresh_rw_0@93@01)
          (< (mod k_fresh_rw_0@93@01 step@43@01) N@41@01)))))
  :pattern (($Seq.index matrix@45@01 k_fresh_rw_0@93@01))
  :qid |prog.l89-aux|)))
(assert (forall ((k_fresh_rw_0@93@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@42@01 step@43@01)) k_fresh_rw_0@93@01)
        (< (mod k_fresh_rw_0@93@01 step@43@01) N@41@01)))
    (=
      ($FVF.lookup_Ref__Integer_value (as sm@83@01  $FVF<Int>) ($Seq.index
        matrix@45@01
        k_fresh_rw_0@93@01))
      ($FVF.lookup_Ref__Integer_value (as sm@66@01  $FVF<Int>) ($Seq.index
        matrix@45@01
        k_fresh_rw_0@93@01))))
  :pattern (($Seq.index matrix@45@01 k_fresh_rw_0@93@01))
  :qid |prog.l89|)))
(pop) ; 2
(push) ; 2
; [exec]
; inhale false
(pop) ; 2
(pop) ; 1
; ---------- Ref__loop_body_113 ----------
(declare-const diz@95@01 $Ref)
(declare-const step@96@01 Int)
(declare-const j@97@01 Int)
(declare-const i@98@01 Int)
(declare-const P@99@01 Int)
(declare-const N@100@01 Int)
(declare-const M@101@01 Int)
(declare-const hist@102@01 $Seq<$Ref>)
(declare-const matrix@103@01 $Seq<$Ref>)
(declare-const diz@104@01 $Ref)
(declare-const step@105@01 Int)
(declare-const j@106@01 Int)
(declare-const i@107@01 Int)
(declare-const P@108@01 Int)
(declare-const N@109@01 Int)
(declare-const M@110@01 Int)
(declare-const hist@111@01 $Seq<$Ref>)
(declare-const matrix@112@01 $Seq<$Ref>)
(push) ; 1
(declare-const $t@113@01 $Snap)
(declare-const $t@114@01 $Snap)
(assert (= $t@113@01 ($Snap.combine $Snap.unit $t@114@01)))
; [eval] diz != null
(assert (not (= diz@104@01 $Ref.null)))
(declare-const $t@115@01 $Snap)
(assert (= $t@114@01 ($Snap.combine $Snap.unit $t@115@01)))
; [eval] M > 0
(assert (> M@110@01 0))
(declare-const $t@116@01 $Snap)
(assert (= $t@115@01 ($Snap.combine $Snap.unit $t@116@01)))
; [eval] N > 0
(assert (> N@109@01 0))
(declare-const $t@117@01 $Snap)
(assert (= $t@116@01 ($Snap.combine $Snap.unit $t@117@01)))
; [eval] step >= N
(assert (>= step@105@01 N@109@01))
(declare-const $t@118@01 $Snap)
(assert (= $t@117@01 ($Snap.combine $Snap.unit $t@118@01)))
; [eval] P > 0
(assert (> P@108@01 0))
(declare-const $t@119@01 $Snap)
(assert (= $t@118@01 ($Snap.combine $Snap.unit $t@119@01)))
; [eval] (i in [0..M))
; [eval] [0..M)
(assert ($Seq.contains ($Seq.range 0 M@110@01) i@107@01))
(declare-const $t@120@01 $Snap)
(assert (= $t@119@01 ($Snap.combine $Snap.unit $t@120@01)))
; [eval] (j in [0..N))
; [eval] [0..N)
(assert ($Seq.contains ($Seq.range 0 N@109@01) j@106@01))
(declare-const $t@121@01 $Snap)
(assert (= $t@120@01 ($Snap.combine $Snap.unit $t@121@01)))
; [eval] P <= |hist|
; [eval] |hist|
(assert (<= P@108@01 ($Seq.length hist@111@01)))
(declare-const $t@122@01 $FVF<Int>)
(declare-const $t@123@01 $Snap)
(assert (=
  $t@121@01
  ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@122@01) $t@123@01)))
(declare-const k@124@01 Int)
(push) ; 2
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@108@01) k@124@01))
; [eval] hist[k]
(push) ; 3
(assert (not (>= k@124@01 0)))
 (set-option :rlimit 19688) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (< k@124@01 ($Seq.length hist@111@01))))
 (set-option :rlimit 3165) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(pop) ; 2
(declare-fun inv@125@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((k@124@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@124@01)
    (= (inv@125@01 ($Seq.index hist@111@01 k@124@01)) k@124@01))
  :pattern (($Seq.index hist@111@01 k@124@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
    (= ($Seq.index hist@111@01 (inv@125@01 r)) r))
  :pattern ((inv@125@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((k@124@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@124@01)
    (not (= ($Seq.index hist@111@01 k@124@01) $Ref.null)))
  :pattern (($Seq.index hist@111@01 k@124@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
(declare-const $t@126@01 $Snap)
(assert (= $t@123@01 ($Snap.combine $Snap.unit $t@126@01)))
; [eval] (forall k: Int :: { (k in [0..P)) } { hist[k] } (k in [0..P)) ==> hist[k].Ref__Integer_value == 0)
(declare-const k@127@01 Int)
(push) ; 2
; [eval] (k in [0..P)) ==> hist[k].Ref__Integer_value == 0
; [eval] (k in [0..P))
; [eval] [0..P)
(push) ; 3
; [then-branch: 11 | k@127@01 in [0..P@108@01] | live]
; [else-branch: 11 | !k@127@01 in [0..P@108@01] | live]
(push) ; 4
; [then-branch: 11 | k@127@01 in [0..P@108@01]]
(assert ($Seq.contains ($Seq.range 0 P@108@01) k@127@01))
; [eval] hist[k].Ref__Integer_value == 0
; [eval] hist[k]
(push) ; 5
(assert (not (>= k@127@01 0)))
 (set-option :rlimit 109339) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(push) ; 5
(assert (not (< k@127@01 ($Seq.length hist@111@01))))
 (set-option :rlimit 201037) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(push) ; 5
(assert (not ($Seq.contains
  ($Seq.range 0 P@108@01)
  (inv@125@01 ($Seq.index hist@111@01 k@127@01)))))
 (set-option :rlimit 28681) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(declare-const sm@128@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r))
    :qid |qp.fvfValDef9|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@122@01 r))
    :qid |qp.fvfValDef9|))))
(pop) ; 4
(push) ; 4
; [else-branch: 11 | !k@127@01 in [0..P@108@01]]
(assert (not ($Seq.contains ($Seq.range 0 P@108@01) k@127@01)))
(pop) ; 4
(pop) ; 3
; Joined path conditions
(assert (implies
  ($Seq.contains ($Seq.range 0 P@108@01) k@127@01)
  (and
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r))
        :qid |qp.fvfValDef9|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@122@01 r))
        :qid |qp.fvfValDef9|)))
    ($Seq.contains ($Seq.range 0 P@108@01) k@127@01))))
; Joined path conditions
(pop) ; 2
; Nested auxiliary terms
(assert (forall ((k@127@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@127@01)
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r))
          :qid |qp.fvfValDef9|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@122@01 r))
          :qid |qp.fvfValDef9|)))
      ($Seq.contains ($Seq.range 0 P@108@01) k@127@01)))
  :pattern (($Seq.contains ($Seq.range 0 P@108@01) k@127@01))
  :qid |prog.l100-aux|)))
(assert (forall ((k@127@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@127@01)
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r))
          :qid |qp.fvfValDef9|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@122@01 r))
          :qid |qp.fvfValDef9|)))
      ($Seq.contains ($Seq.range 0 P@108@01) k@127@01)))
  :pattern (($Seq.index hist@111@01 k@127@01))
  :qid |prog.l100-aux|)))
(assert (and
  (forall ((k@127@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) k@127@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) ($Seq.index
          hist@111@01
          k@127@01))
        0))
    :pattern (($Seq.contains ($Seq.range 0 P@108@01) k@127@01))
    :qid |prog.l100|))
  (forall ((k@127@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) k@127@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@128@01  $FVF<Int>) ($Seq.index
          hist@111@01
          k@127@01))
        0))
    :pattern (($Seq.index hist@111@01 k@127@01))
    :qid |prog.l100|))))
(declare-const $t@129@01 $Snap)
(assert (= $t@126@01 ($Snap.combine $Snap.unit $t@129@01)))
; [eval] i * step + j < |matrix|
; [eval] i * step + j
; [eval] i * step
; [eval] |matrix|
(assert (< (+ (* i@107@01 step@105@01) j@106@01) ($Seq.length matrix@112@01)))
(declare-const $t@130@01 Int)
(assert (= $t@129@01 ($Snap.combine ($SortWrappers.IntTo$Snap $t@130@01) $Snap.unit)))
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
(push) ; 2
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 458) (check-sat) 
; unsat
(pop) ; 2
; 0.01s
; 
(push) ; 2
(assert (not (not (= 4 0))))
 (set-option :rlimit 39183) (check-sat) 
; unsat
(pop) ; 2
; 0.00s
; 
(declare-const sm@131@01 $FVF<Int>)
; Definitional axioms for singleton-SM's value
(assert (=
  ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) ($Seq.index
    matrix@112@01
    (+ (* i@107@01 step@105@01) j@106@01)))
  $t@130@01))
(assert (<=
  $Perm.No
  (ite
    (=
      ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
      ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
    (/ (to_real 1) (to_real 4))
    $Perm.No)))
(assert (<=
  (ite
    (=
      ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
      ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
    (/ (to_real 1) (to_real 4))
    $Perm.No)
  $Perm.Write))
(assert (implies
  (=
    ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
    ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
  (not
    (=
      ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
      $Ref.null))))
; [eval] (matrix[i * step + j].Ref__Integer_value in [0..P))
; [eval] [0..P)
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
(push) ; 2
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 55819) (check-sat) 
; unsat
(pop) ; 2
; 0.00s
; 
(push) ; 2
(assert (not (<
  $Perm.No
  (+
    (ite
      (=
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)
    (ite
      ($Seq.contains
        ($Seq.range 0 P@108@01)
        (inv@125@01 ($Seq.index
          matrix@112@01
          (+ (* i@107@01 step@105@01) j@106@01))))
      $Perm.Write
      $Perm.No)))))
 (set-option :rlimit 4022) (check-sat) 
; unsat
(pop) ; 2
; 0.00s
; 
(declare-const sm@132@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) r))
    :qid |qp.fvfValDef10|))
  (forall ((r $Ref)) (!
    (implies
      (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r))
    :qid |qp.fvfValDef10|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) r))
    :qid |qp.fvfValDef11|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@122@01 r))
    :qid |qp.fvfValDef11|))))
(assert ($Seq.contains
  ($Seq.range 0 P@108@01)
  ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) ($Seq.index
    matrix@112@01
    (+ (* i@107@01 step@105@01) j@106@01)))))
; State saturation: after contract
;(set-option :timeout 50)
 (set-option :rlimit 167148) (check-sat) 
; unknown
(push) ; 2
(declare-const $t@133@01 $Snap)
(declare-const $t@134@01 $Snap)
(assert (= $t@133@01 ($Snap.combine $Snap.unit $t@134@01)))
; [eval] M > 0
(declare-const $t@135@01 $Snap)
(assert (= $t@134@01 ($Snap.combine $Snap.unit $t@135@01)))
; [eval] N > 0
(declare-const $t@136@01 $Snap)
(assert (= $t@135@01 ($Snap.combine $Snap.unit $t@136@01)))
; [eval] step >= N
(declare-const $t@137@01 $Snap)
(assert (= $t@136@01 ($Snap.combine $Snap.unit $t@137@01)))
; [eval] P > 0
(declare-const $t@138@01 $Snap)
(assert (= $t@137@01 ($Snap.combine $Snap.unit $t@138@01)))
; [eval] (i in [0..M))
; [eval] [0..M)
(declare-const $t@139@01 $Snap)
(assert (= $t@138@01 ($Snap.combine $Snap.unit $t@139@01)))
; [eval] (j in [0..N))
; [eval] [0..N)
(declare-const $t@140@01 Int)
(declare-const $t@141@01 $Snap)
(assert (= $t@139@01 ($Snap.combine ($SortWrappers.IntTo$Snap $t@140@01) $t@141@01)))
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
;(set-option :timeout 0)
(push) ; 3
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 6991) (check-sat) 
; unsat
(pop) ; 3
; 0.01s
; 
(push) ; 3
(assert (not (not (= 4 0))))
 (set-option :rlimit 2758) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(declare-const sm@142@01 $FVF<Int>)
; Definitional axioms for singleton-SM's value
(assert (=
  ($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) ($Seq.index
    matrix@112@01
    (+ (* i@107@01 step@105@01) j@106@01)))
  $t@140@01))
(declare-const $t@143@01 $FVF<Int>)
(assert (=
  $t@141@01
  ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@143@01) $Snap.unit)))
(declare-const k@144@01 Int)
(push) ; 3
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@108@01) k@144@01))
; [eval] hist[k]
(push) ; 4
(assert (not (>= k@144@01 0)))
 (set-option :rlimit 28036) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< k@144@01 ($Seq.length hist@111@01))))
 (set-option :rlimit 1569) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@145@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((k@144@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@144@01)
    (= (inv@145@01 ($Seq.index hist@111@01 k@144@01)) k@144@01))
  :pattern (($Seq.index hist@111@01 k@144@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) (inv@145@01 r))
    (= ($Seq.index hist@111@01 (inv@145@01 r)) r))
  :pattern ((inv@145@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((k@144@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@144@01)
    (not (= ($Seq.index hist@111@01 k@144@01) $Ref.null)))
  :pattern (($Seq.index hist@111@01 k@144@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
; [eval] (forall k: Int :: { (k in [0..P)) } { hist[k] } (k in [0..P)) ==> hist[k].Ref__Integer_value == (matrix[i * step + j].Ref__Integer_value == k ? 1 : 0))
(declare-const k@146@01 Int)
(push) ; 3
; [eval] (k in [0..P)) ==> hist[k].Ref__Integer_value == (matrix[i * step + j].Ref__Integer_value == k ? 1 : 0)
; [eval] (k in [0..P))
; [eval] [0..P)
(push) ; 4
; [then-branch: 12 | k@146@01 in [0..P@108@01] | live]
; [else-branch: 12 | !k@146@01 in [0..P@108@01] | live]
(push) ; 5
; [then-branch: 12 | k@146@01 in [0..P@108@01]]
(assert ($Seq.contains ($Seq.range 0 P@108@01) k@146@01))
; [eval] hist[k].Ref__Integer_value == (matrix[i * step + j].Ref__Integer_value == k ? 1 : 0)
; [eval] hist[k]
(push) ; 6
(assert (not (>= k@146@01 0)))
 (set-option :rlimit 72668) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k@146@01 ($Seq.length hist@111@01))))
 (set-option :rlimit 32905) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@108@01)
        (inv@145@01 ($Seq.index hist@111@01 k@146@01)))
      $Perm.Write
      $Perm.No)
    (ite
      (=
        ($Seq.index hist@111@01 k@146@01)
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)))))
 (set-option :rlimit 5463) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(declare-const sm@147@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) (inv@145@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@143@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r))
    :qid |qp.fvfValDef12|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) (inv@145@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@143@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@143@01 r))
    :qid |qp.fvfValDef12|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r))
    :qid |qp.fvfValDef13|))
  (forall ((r $Ref)) (!
    (implies
      (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r))
    :qid |qp.fvfValDef13|))))
; [eval] (matrix[i * step + j].Ref__Integer_value == k ? 1 : 0)
; [eval] matrix[i * step + j].Ref__Integer_value == k
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
(push) ; 6
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 15787) (check-sat) 
; unsat
(pop) ; 6
; 0.01s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@108@01)
        (inv@145@01 ($Seq.index
          matrix@112@01
          (+ (* i@107@01 step@105@01) j@106@01))))
      $Perm.Write
      $Perm.No)
    (ite
      (=
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)))))
 (set-option :rlimit 9703) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
; [then-branch: 13 | Lookup(Ref__Integer_value,sm@147@01,matrix@112@01[i@107@01 * step@105@01 + j@106@01]) == k@146@01 | live]
; [else-branch: 13 | Lookup(Ref__Integer_value,sm@147@01,matrix@112@01[i@107@01 * step@105@01 + j@106@01]) != k@146@01 | live]
(push) ; 7
; [then-branch: 13 | Lookup(Ref__Integer_value,sm@147@01,matrix@112@01[i@107@01 * step@105@01 + j@106@01]) == k@146@01]
(assert (=
  ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) ($Seq.index
    matrix@112@01
    (+ (* i@107@01 step@105@01) j@106@01)))
  k@146@01))
(pop) ; 7
(push) ; 7
; [else-branch: 13 | Lookup(Ref__Integer_value,sm@147@01,matrix@112@01[i@107@01 * step@105@01 + j@106@01]) != k@146@01]
(assert (not
  (=
    ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) ($Seq.index
      matrix@112@01
      (+ (* i@107@01 step@105@01) j@106@01)))
    k@146@01)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(pop) ; 5
(push) ; 5
; [else-branch: 12 | !k@146@01 in [0..P@108@01]]
(assert (not ($Seq.contains ($Seq.range 0 P@108@01) k@146@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (implies
  ($Seq.contains ($Seq.range 0 P@108@01) k@146@01)
  (and
    (and
      (forall ((r $Ref)) (!
        (implies
          (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r))
        :qid |qp.fvfValDef13|))
      (forall ((r $Ref)) (!
        (implies
          (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r))
        :qid |qp.fvfValDef13|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@108@01) (inv@145@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@143@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r))
        :qid |qp.fvfValDef12|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@108@01) (inv@145@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@143@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@143@01 r))
        :qid |qp.fvfValDef12|)))
    ($Seq.contains ($Seq.range 0 P@108@01) k@146@01))))
; Joined path conditions
(pop) ; 3
; Nested auxiliary terms
(assert (forall ((k@146@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@146@01)
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r))
          :qid |qp.fvfValDef13|))
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r))
          :qid |qp.fvfValDef13|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@145@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@143@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r))
          :qid |qp.fvfValDef12|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@145@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@143@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@143@01 r))
          :qid |qp.fvfValDef12|)))
      ($Seq.contains ($Seq.range 0 P@108@01) k@146@01)))
  :pattern (($Seq.contains ($Seq.range 0 P@108@01) k@146@01))
  :qid |prog.l108-aux|)))
(assert (forall ((k@146@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@146@01)
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r))
          :qid |qp.fvfValDef13|))
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r))
          :qid |qp.fvfValDef13|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@145@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@143@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r))
          :qid |qp.fvfValDef12|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@145@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@143@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@143@01 r))
          :qid |qp.fvfValDef12|)))
      ($Seq.contains ($Seq.range 0 P@108@01) k@146@01)))
  :pattern (($Seq.index hist@111@01 k@146@01))
  :qid |prog.l108-aux|)))
(assert (and
  (forall ((k@146@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) k@146@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) ($Seq.index
          hist@111@01
          k@146@01))
        (ite
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) ($Seq.index
              matrix@112@01
              (+ (* i@107@01 step@105@01) j@106@01)))
            k@146@01)
          1
          0)))
    :pattern (($Seq.contains ($Seq.range 0 P@108@01) k@146@01))
    :qid |prog.l108|))
  (forall ((k@146@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) k@146@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) ($Seq.index
          hist@111@01
          k@146@01))
        (ite
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) ($Seq.index
              matrix@112@01
              (+ (* i@107@01 step@105@01) j@106@01)))
            k@146@01)
          1
          0)))
    :pattern (($Seq.index hist@111@01 k@146@01))
    :qid |prog.l108|))))
; [eval] matrix[i * step + j].Ref__Integer_value == old(matrix[i * step + j].Ref__Integer_value)
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
(push) ; 3
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 28312) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@108@01)
        (inv@145@01 ($Seq.index
          matrix@112@01
          (+ (* i@107@01 step@105@01) j@106@01))))
      $Perm.Write
      $Perm.No)
    (ite
      (=
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)))))
 (set-option :rlimit 1458) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) (inv@145@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@143@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r))
    :qid |qp.fvfValDef12|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) (inv@145@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@143@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@143@01 r))
    :qid |qp.fvfValDef12|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r))
    :qid |qp.fvfValDef13|))
  (forall ((r $Ref)) (!
    (implies
      (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@142@01  $FVF<Int>) r))
    :qid |qp.fvfValDef13|))))
; [eval] old(matrix[i * step + j].Ref__Integer_value)
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
(push) ; 3
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 2364) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (<
  $Perm.No
  (+
    (ite
      (=
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)
    (ite
      ($Seq.contains
        ($Seq.range 0 P@108@01)
        (inv@125@01 ($Seq.index
          matrix@112@01
          (+ (* i@107@01 step@105@01) j@106@01))))
      $Perm.Write
      $Perm.No)))))
 (set-option :rlimit 491982) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(assert (=
  ($FVF.lookup_Ref__Integer_value (as sm@147@01  $FVF<Int>) ($Seq.index
    matrix@112@01
    (+ (* i@107@01 step@105@01) j@106@01)))
  ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) ($Seq.index
    matrix@112@01
    (+ (* i@107@01 step@105@01) j@106@01)))))
(pop) ; 2
(push) ; 2
; [exec]
; var __flatten_4: Ref
(declare-const __flatten_4@148@01 $Ref)
; [exec]
; var __flatten_5: Ref
(declare-const __flatten_5@149@01 $Ref)
; [exec]
; var __flatten_6: Int
(declare-const __flatten_6@150@01 Int)
; [exec]
; var __flatten_7: Ref
(declare-const __flatten_7@151@01 $Ref)
; [exec]
; var __flatten_8: Ref
(declare-const __flatten_8@152@01 $Ref)
; [exec]
; __flatten_4 := matrix[i * step + j]
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
(push) ; 3
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 1200) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(declare-const __flatten_4@153@01 $Ref)
(assert (=
  __flatten_4@153@01
  ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))))
; [exec]
; __flatten_5 := hist[__flatten_4.Ref__Integer_value]
; [eval] hist[__flatten_4.Ref__Integer_value]
(push) ; 3
(assert (not (<
  $Perm.No
  (+
    (ite
      (=
        __flatten_4@153@01
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)
    (ite
      ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 __flatten_4@153@01))
      $Perm.Write
      $Perm.No)))))
 (set-option :rlimit 51148) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (>=
  ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)
  0)))
 (set-option :rlimit 124756) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (<
  ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)
  ($Seq.length hist@111@01))))
 (set-option :rlimit 28123) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; [exec]
; __flatten_7 := matrix[i * step + j]
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
(push) ; 3
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 6200) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(declare-const __flatten_7@154@01 $Ref)
(assert (=
  __flatten_7@154@01
  ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))))
; [exec]
; __flatten_8 := hist[__flatten_7.Ref__Integer_value]
; [eval] hist[__flatten_7.Ref__Integer_value]
(push) ; 3
(assert (not (<
  $Perm.No
  (+
    (ite
      (=
        __flatten_7@154@01
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)
    (ite
      ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 __flatten_7@154@01))
      $Perm.Write
      $Perm.No)))))
 (set-option :rlimit 849) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (>=
  ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_7@154@01)
  0)))
 (set-option :rlimit 29041) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (<
  ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_7@154@01)
  ($Seq.length hist@111@01))))
 (set-option :rlimit 2197) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; [exec]
; __flatten_6 := __flatten_8.Ref__Integer_value + 1
; [eval] __flatten_8.Ref__Integer_value + 1
(push) ; 3
(assert (not (<
  $Perm.No
  (+
    (ite
      (=
        ($Seq.index
          hist@111@01
          ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_7@154@01))
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)
    (ite
      ($Seq.contains
        ($Seq.range 0 P@108@01)
        (inv@125@01 ($Seq.index
          hist@111@01
          ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_7@154@01))))
      $Perm.Write
      $Perm.No)))))
 (set-option :rlimit 4968) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(declare-const __flatten_6@155@01 Int)
(assert (=
  __flatten_6@155@01
  (+
    ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) ($Seq.index
      hist@111@01
      ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_7@154@01)))
    1)))
; [exec]
; __flatten_5.Ref__Integer_value := __flatten_6
; Precomputing data for removing quantified permissions
(define-fun pTaken@156@01 ((r $Ref)) $Perm
  (ite
    (=
      r
      ($Seq.index
        hist@111@01
        ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
    ($Perm.min
      (ite
        ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
(define-fun pTaken@157@01 ((r $Ref)) $Perm
  (ite
    (=
      r
      ($Seq.index
        hist@111@01
        ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
    ($Perm.min
      (ite
        (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
        (/ (to_real 1) (to_real 4))
        $Perm.No)
      (- $Perm.Write (pTaken@156@01 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
;(set-option :timeout 10)
 (set-option :rlimit 830598) (check-sat) 
; unknown
; Chunk depleted?
;(set-option :timeout 500)
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (ite
        ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
        $Perm.Write
        $Perm.No)
      (pTaken@156@01 r))
    $Perm.No)
  
  ))))
 (set-option :rlimit 4471) (check-sat) 
; unknown
(pop) ; 3
; 0.02s
; 
; Intermediate check if already taken enough permissions
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (implies
    (=
      r
      ($Seq.index
        hist@111@01
        ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
    (= (- $Perm.Write (pTaken@156@01 r)) $Perm.No))
  
  ))))
 (set-option :rlimit 25084) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@158@01 $FVF<Int>)
; Definitional axioms for singleton-FVF's value
(assert (=
  ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) ($Seq.index
    hist@111@01
    ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
  __flatten_6@155@01))
; [eval] M > 0
; [eval] N > 0
; [eval] step >= N
; [eval] P > 0
; [eval] (i in [0..M))
; [eval] [0..M)
; [eval] (j in [0..N))
; [eval] [0..N)
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
;(set-option :timeout 0)
(push) ; 3
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 60149) (check-sat) 
; unsat
(pop) ; 3
; 0.04s
; 
(push) ; 3
(assert (not (not (= 4 0))))
 (set-option :rlimit 13523) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Precomputing data for removing quantified permissions
(define-fun pTaken@159@01 ((r $Ref)) $Perm
  (ite
    (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
    ($Perm.min
      (ite
        (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
        (/ (to_real 1) (to_real 4))
        $Perm.No)
      (/ (to_real 1) (to_real 4)))
    $Perm.No))
(define-fun pTaken@160@01 ((r $Ref)) $Perm
  (ite
    (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
    ($Perm.min
      (ite
        (=
          r
          ($Seq.index
            hist@111@01
            ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
        $Perm.Write
        $Perm.No)
      (- (/ (to_real 1) (to_real 4)) (pTaken@159@01 r)))
    $Perm.No))
(define-fun pTaken@161@01 ((r $Ref)) $Perm
  (ite
    (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
    ($Perm.min
      (-
        (ite
          ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
          $Perm.Write
          $Perm.No)
        (pTaken@156@01 r))
      (- (- (/ (to_real 1) (to_real 4)) (pTaken@159@01 r)) (pTaken@160@01 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
;(set-option :timeout 10)
 (set-option :rlimit 72340) (check-sat) 
; unknown
; Chunk depleted?
;(set-option :timeout 500)
(push) ; 3
(assert (not (=
  (-
    (ite
      (=
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)
    (pTaken@159@01 ($Seq.index
      matrix@112@01
      (+ (* i@107@01 step@105@01) j@106@01))))
  $Perm.No)))
 (set-option :rlimit 109393) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Intermediate check if already taken enough permissions
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (implies
    (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
    (= (- (/ (to_real 1) (to_real 4)) (pTaken@159@01 r)) $Perm.No))
  
  ))))
 (set-option :rlimit 7943) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@162@01 $FVF<Int>)
; Definitional axioms for singleton-SM's value
(assert (implies
  (=
    ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
    ($Seq.index
      hist@111@01
      ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
  (=
    ($FVF.lookup_Ref__Integer_value (as sm@162@01  $FVF<Int>) ($Seq.index
      matrix@112@01
      (+ (* i@107@01 step@105@01) j@106@01)))
    ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) ($Seq.index
      matrix@112@01
      (+ (* i@107@01 step@105@01) j@106@01))))))
(assert (implies
  (=
    ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
    ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
  (=
    ($FVF.lookup_Ref__Integer_value (as sm@162@01  $FVF<Int>) ($Seq.index
      matrix@112@01
      (+ (* i@107@01 step@105@01) j@106@01)))
    ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) ($Seq.index
      matrix@112@01
      (+ (* i@107@01 step@105@01) j@106@01))))))
(assert (implies
  (<
    $Perm.No
    (-
      (ite
        ($Seq.contains
          ($Seq.range 0 P@108@01)
          (inv@125@01 ($Seq.index
            matrix@112@01
            (+ (* i@107@01 step@105@01) j@106@01))))
        $Perm.Write
        $Perm.No)
      (pTaken@156@01 ($Seq.index
        matrix@112@01
        (+ (* i@107@01 step@105@01) j@106@01)))))
  (=
    ($FVF.lookup_Ref__Integer_value (as sm@162@01  $FVF<Int>) ($Seq.index
      matrix@112@01
      (+ (* i@107@01 step@105@01) j@106@01)))
    ($FVF.lookup_Ref__Integer_value $t@122@01 ($Seq.index
      matrix@112@01
      (+ (* i@107@01 step@105@01) j@106@01))))))
(declare-const k@163@01 Int)
(push) ; 3
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@108@01) k@163@01))
; [eval] hist[k]
;(set-option :timeout 0)
(push) ; 4
(assert (not (>= k@163@01 0)))
 (set-option :rlimit 26098) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< k@163@01 ($Seq.length hist@111@01))))
 (set-option :rlimit 134712) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@164@01 ($Ref) Int)
; Nested auxiliary terms
(push) ; 3
(assert (not (forall ((k@163@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@163@01)
    (or (= $Perm.Write $Perm.No) true))
  
  ))))
 (set-option :rlimit 8527) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Check receiver injectivity
(push) ; 3
(assert (not (forall ((k1@163@01 Int) (k2@163@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 P@108@01) k1@163@01)
      ($Seq.contains ($Seq.range 0 P@108@01) k2@163@01)
      (= ($Seq.index hist@111@01 k1@163@01) ($Seq.index hist@111@01 k2@163@01)))
    (= k1@163@01 k2@163@01))
  
  :qid |Ref__Integer_value-rcvrInj|))))
 (set-option :rlimit 14227) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Definitional axioms for inverse functions
(assert (forall ((k@163@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@163@01)
    (= (inv@164@01 ($Seq.index hist@111@01 k@163@01)) k@163@01))
  :pattern (($Seq.index hist@111@01 k@163@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) (inv@164@01 r))
    (= ($Seq.index hist@111@01 (inv@164@01 r)) r))
  :pattern ((inv@164@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@165@01 ((r $Ref)) $Perm
  (ite
    ($Seq.contains ($Seq.range 0 P@108@01) (inv@164@01 r))
    ($Perm.min
      (-
        (ite
          ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
          $Perm.Write
          $Perm.No)
        (pTaken@156@01 r))
      $Perm.Write)
    $Perm.No))
(define-fun pTaken@166@01 ((r $Ref)) $Perm
  (ite
    ($Seq.contains ($Seq.range 0 P@108@01) (inv@164@01 r))
    ($Perm.min
      (ite
        (=
          r
          ($Seq.index
            hist@111@01
            ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
        $Perm.Write
        $Perm.No)
      (- $Perm.Write (pTaken@165@01 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
;(set-option :timeout 10)
 (set-option :rlimit 23988) (check-sat) 
; unknown
; Chunk depleted?
;(set-option :timeout 500)
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (-
        (ite
          ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
          $Perm.Write
          $Perm.No)
        (pTaken@156@01 r))
      (pTaken@165@01 r))
    $Perm.No)
  
  ))))
 (set-option :rlimit 99459) (check-sat) 
; unsat
(pop) ; 3
; 0.01s
; 
; Intermediate check if already taken enough permissions
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) (inv@164@01 r))
    (= (- $Perm.Write (pTaken@165@01 r)) $Perm.No))
  
  ))))
 (set-option :rlimit 48990) (check-sat) 
; unknown
(pop) ; 3
; 0.01s
; 
; Chunk depleted?
(push) ; 3
(assert (not (=
  (-
    (ite
      (=
        ($Seq.index
          hist@111@01
          ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01))
        ($Seq.index
          hist@111@01
          ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
      $Perm.Write
      $Perm.No)
    (pTaken@166@01 ($Seq.index
      hist@111@01
      ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01))))
  $Perm.No)))
 (set-option :rlimit 32734) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Intermediate check if already taken enough permissions
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) (inv@164@01 r))
    (= (- (- $Perm.Write (pTaken@165@01 r)) (pTaken@166@01 r)) $Perm.No))
  
  ))))
 (set-option :rlimit 11339) (check-sat) 
; unsat
(pop) ; 3
; 0.01s
; 
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@167@01 $FVF<Int>)
; Definitional axioms for SM values
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (<
        $Perm.No
        (-
          (ite
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
            $Perm.Write
            $Perm.No)
          (pTaken@156@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@167@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@167@01  $FVF<Int>) r))
    :qid |qp.fvfValDef17|))
  (forall ((r $Ref)) (!
    (implies
      (<
        $Perm.No
        (-
          (ite
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
            $Perm.Write
            $Perm.No)
          (pTaken@156@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@167@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@122@01 r))
    :qid |qp.fvfValDef17|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (=
        r
        ($Seq.index
          hist@111@01
          ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@167@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@167@01  $FVF<Int>) r))
    :qid |qp.fvfValDef18|))
  (forall ((r $Ref)) (!
    (implies
      (=
        r
        ($Seq.index
          hist@111@01
          ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@167@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r))
    :qid |qp.fvfValDef18|))))
; [eval] (forall k: Int :: { (k in [0..P)) } { hist[k] } (k in [0..P)) ==> hist[k].Ref__Integer_value == (matrix[i * step + j].Ref__Integer_value == k ? 1 : 0))
(declare-const k@168@01 Int)
(push) ; 3
; [eval] (k in [0..P)) ==> hist[k].Ref__Integer_value == (matrix[i * step + j].Ref__Integer_value == k ? 1 : 0)
; [eval] (k in [0..P))
; [eval] [0..P)
(push) ; 4
; [then-branch: 14 | k@168@01 in [0..P@108@01] | live]
; [else-branch: 14 | !k@168@01 in [0..P@108@01] | live]
(push) ; 5
; [then-branch: 14 | k@168@01 in [0..P@108@01]]
(assert ($Seq.contains ($Seq.range 0 P@108@01) k@168@01))
; [eval] hist[k].Ref__Integer_value == (matrix[i * step + j].Ref__Integer_value == k ? 1 : 0)
; [eval] hist[k]
;(set-option :timeout 0)
(push) ; 6
(assert (not (>= k@168@01 0)))
 (set-option :rlimit 129316) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k@168@01 ($Seq.length hist@111@01))))
 (set-option :rlimit 25039) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (=
          ($Seq.index hist@111@01 k@168@01)
          ($Seq.index
            hist@111@01
            ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
        $Perm.Write
        $Perm.No)
      (ite
        (=
          ($Seq.index hist@111@01 k@168@01)
          ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
        (/ (to_real 1) (to_real 4))
        $Perm.No))
    (-
      (ite
        ($Seq.contains
          ($Seq.range 0 P@108@01)
          (inv@125@01 ($Seq.index hist@111@01 k@168@01)))
        $Perm.Write
        $Perm.No)
      (pTaken@156@01 ($Seq.index hist@111@01 k@168@01)))))))
 (set-option :rlimit 1013) (check-sat) 
; unsat
(pop) ; 6
; 0.01s
; 
(declare-const sm@169@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (=
        r
        ($Seq.index
          hist@111@01
          ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
    :qid |qp.fvfValDef19|))
  (forall ((r $Ref)) (!
    (implies
      (=
        r
        ($Seq.index
          hist@111@01
          ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r))
    :qid |qp.fvfValDef19|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
    :qid |qp.fvfValDef20|))
  (forall ((r $Ref)) (!
    (implies
      (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r))
    :qid |qp.fvfValDef20|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (<
        $Perm.No
        (-
          (ite
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
            $Perm.Write
            $Perm.No)
          (pTaken@156@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
    :qid |qp.fvfValDef21|))
  (forall ((r $Ref)) (!
    (implies
      (<
        $Perm.No
        (-
          (ite
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
            $Perm.Write
            $Perm.No)
          (pTaken@156@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@122@01 r))
    :qid |qp.fvfValDef21|))))
; [eval] (matrix[i * step + j].Ref__Integer_value == k ? 1 : 0)
; [eval] matrix[i * step + j].Ref__Integer_value == k
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
(push) ; 6
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 12706) (check-sat) 
; unsat
(pop) ; 6
; 0.04s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (=
          ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
          ($Seq.index
            hist@111@01
            ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
        $Perm.Write
        $Perm.No)
      (ite
        (=
          ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
          ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
        (/ (to_real 1) (to_real 4))
        $Perm.No))
    (-
      (ite
        ($Seq.contains
          ($Seq.range 0 P@108@01)
          (inv@125@01 ($Seq.index
            matrix@112@01
            (+ (* i@107@01 step@105@01) j@106@01))))
        $Perm.Write
        $Perm.No)
      (pTaken@156@01 ($Seq.index
        matrix@112@01
        (+ (* i@107@01 step@105@01) j@106@01))))))))
 (set-option :rlimit 26113) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
; [then-branch: 15 | Lookup(Ref__Integer_value,sm@169@01,matrix@112@01[i@107@01 * step@105@01 + j@106@01]) == k@168@01 | live]
; [else-branch: 15 | Lookup(Ref__Integer_value,sm@169@01,matrix@112@01[i@107@01 * step@105@01 + j@106@01]) != k@168@01 | live]
(push) ; 7
; [then-branch: 15 | Lookup(Ref__Integer_value,sm@169@01,matrix@112@01[i@107@01 * step@105@01 + j@106@01]) == k@168@01]
(assert (=
  ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
    matrix@112@01
    (+ (* i@107@01 step@105@01) j@106@01)))
  k@168@01))
(pop) ; 7
(push) ; 7
; [else-branch: 15 | Lookup(Ref__Integer_value,sm@169@01,matrix@112@01[i@107@01 * step@105@01 + j@106@01]) != k@168@01]
(assert (not
  (=
    ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
      matrix@112@01
      (+ (* i@107@01 step@105@01) j@106@01)))
    k@168@01)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(pop) ; 5
(push) ; 5
; [else-branch: 14 | !k@168@01 in [0..P@108@01]]
(assert (not ($Seq.contains ($Seq.range 0 P@108@01) k@168@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (implies
  ($Seq.contains ($Seq.range 0 P@108@01) k@168@01)
  (and
    (and
      (forall ((r $Ref)) (!
        (implies
          (<
            $Perm.No
            (-
              (ite
                ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
                $Perm.Write
                $Perm.No)
              (pTaken@156@01 r)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
        :qid |qp.fvfValDef21|))
      (forall ((r $Ref)) (!
        (implies
          (<
            $Perm.No
            (-
              (ite
                ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
                $Perm.Write
                $Perm.No)
              (pTaken@156@01 r)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@122@01 r))
        :qid |qp.fvfValDef21|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
        :qid |qp.fvfValDef20|))
      (forall ((r $Ref)) (!
        (implies
          (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r))
        :qid |qp.fvfValDef20|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (=
            r
            ($Seq.index
              hist@111@01
              ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
        :qid |qp.fvfValDef19|))
      (forall ((r $Ref)) (!
        (implies
          (=
            r
            ($Seq.index
              hist@111@01
              ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r))
        :qid |qp.fvfValDef19|)))
    ($Seq.contains ($Seq.range 0 P@108@01) k@168@01))))
; Joined path conditions
(pop) ; 3
; Nested auxiliary terms
(assert (forall ((k@168@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@168@01)
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (<
              $Perm.No
              (-
                (ite
                  ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
                  $Perm.Write
                  $Perm.No)
                (pTaken@156@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
          :qid |qp.fvfValDef21|))
        (forall ((r $Ref)) (!
          (implies
            (<
              $Perm.No
              (-
                (ite
                  ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
                  $Perm.Write
                  $Perm.No)
                (pTaken@156@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@122@01 r))
          :qid |qp.fvfValDef21|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
          :qid |qp.fvfValDef20|))
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r))
          :qid |qp.fvfValDef20|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index
                hist@111@01
                ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
          :qid |qp.fvfValDef19|))
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index
                hist@111@01
                ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r))
          :qid |qp.fvfValDef19|)))
      ($Seq.contains ($Seq.range 0 P@108@01) k@168@01)))
  :pattern (($Seq.contains ($Seq.range 0 P@108@01) k@168@01))
  :qid |prog.l108-aux|)))
(assert (forall ((k@168@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@108@01) k@168@01)
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (<
              $Perm.No
              (-
                (ite
                  ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
                  $Perm.Write
                  $Perm.No)
                (pTaken@156@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
          :qid |qp.fvfValDef21|))
        (forall ((r $Ref)) (!
          (implies
            (<
              $Perm.No
              (-
                (ite
                  ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
                  $Perm.Write
                  $Perm.No)
                (pTaken@156@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@122@01 r))
          :qid |qp.fvfValDef21|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
          :qid |qp.fvfValDef20|))
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r))
          :qid |qp.fvfValDef20|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index
                hist@111@01
                ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
          :qid |qp.fvfValDef19|))
        (forall ((r $Ref)) (!
          (implies
            (=
              r
              ($Seq.index
                hist@111@01
                ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r))
          :qid |qp.fvfValDef19|)))
      ($Seq.contains ($Seq.range 0 P@108@01) k@168@01)))
  :pattern (($Seq.index hist@111@01 k@168@01))
  :qid |prog.l108-aux|)))
(push) ; 3
(assert (not (and
  (forall ((k@168@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) k@168@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
          hist@111@01
          k@168@01))
        (ite
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
              matrix@112@01
              (+ (* i@107@01 step@105@01) j@106@01)))
            k@168@01)
          1
          0)))
    :pattern (($Seq.contains ($Seq.range 0 P@108@01) k@168@01))
    :qid |prog.l108|))
  (forall ((k@168@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) k@168@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
          hist@111@01
          k@168@01))
        (ite
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
              matrix@112@01
              (+ (* i@107@01 step@105@01) j@106@01)))
            k@168@01)
          1
          0)))
    :pattern (($Seq.index hist@111@01 k@168@01))
    :qid |prog.l108|)))))
 (set-option :rlimit 49281) (check-sat) 
; unsat
(pop) ; 3
; 0.03s
; 
(assert (and
  (forall ((k@168@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) k@168@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
          hist@111@01
          k@168@01))
        (ite
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
              matrix@112@01
              (+ (* i@107@01 step@105@01) j@106@01)))
            k@168@01)
          1
          0)))
    :pattern (($Seq.contains ($Seq.range 0 P@108@01) k@168@01))
    :qid |prog.l108|))
  (forall ((k@168@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@108@01) k@168@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
          hist@111@01
          k@168@01))
        (ite
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
              matrix@112@01
              (+ (* i@107@01 step@105@01) j@106@01)))
            k@168@01)
          1
          0)))
    :pattern (($Seq.index hist@111@01 k@168@01))
    :qid |prog.l108|))))
; [eval] matrix[i * step + j].Ref__Integer_value == old(matrix[i * step + j].Ref__Integer_value)
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
(push) ; 3
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 308448) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (=
          ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
          ($Seq.index
            hist@111@01
            ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
        $Perm.Write
        $Perm.No)
      (ite
        (=
          ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
          ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
        (/ (to_real 1) (to_real 4))
        $Perm.No))
    (-
      (ite
        ($Seq.contains
          ($Seq.range 0 P@108@01)
          (inv@125@01 ($Seq.index
            matrix@112@01
            (+ (* i@107@01 step@105@01) j@106@01))))
        $Perm.Write
        $Perm.No)
      (pTaken@156@01 ($Seq.index
        matrix@112@01
        (+ (* i@107@01 step@105@01) j@106@01))))))))
 (set-option :rlimit 129796) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (=
        r
        ($Seq.index
          hist@111@01
          ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
    :qid |qp.fvfValDef19|))
  (forall ((r $Ref)) (!
    (implies
      (=
        r
        ($Seq.index
          hist@111@01
          ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) __flatten_4@153@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@158@01  $FVF<Int>) r))
    :qid |qp.fvfValDef19|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
    :qid |qp.fvfValDef20|))
  (forall ((r $Ref)) (!
    (implies
      (= r ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@131@01  $FVF<Int>) r))
    :qid |qp.fvfValDef20|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (<
        $Perm.No
        (-
          (ite
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
            $Perm.Write
            $Perm.No)
          (pTaken@156@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r))
    :qid |qp.fvfValDef21|))
  (forall ((r $Ref)) (!
    (implies
      (<
        $Perm.No
        (-
          (ite
            ($Seq.contains ($Seq.range 0 P@108@01) (inv@125@01 r))
            $Perm.Write
            $Perm.No)
          (pTaken@156@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@122@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@122@01 r))
    :qid |qp.fvfValDef21|))))
; [eval] old(matrix[i * step + j].Ref__Integer_value)
; [eval] matrix[i * step + j]
; [eval] i * step + j
; [eval] i * step
(push) ; 3
(assert (not (>= (+ (* i@107@01 step@105@01) j@106@01) 0)))
 (set-option :rlimit 24084) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (<
  $Perm.No
  (+
    (ite
      (=
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01))
        ($Seq.index matrix@112@01 (+ (* i@107@01 step@105@01) j@106@01)))
      (/ (to_real 1) (to_real 4))
      $Perm.No)
    (ite
      ($Seq.contains
        ($Seq.range 0 P@108@01)
        (inv@125@01 ($Seq.index
          matrix@112@01
          (+ (* i@107@01 step@105@01) j@106@01))))
      $Perm.Write
      $Perm.No)))))
 (set-option :rlimit 14408) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (=
  ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
    matrix@112@01
    (+ (* i@107@01 step@105@01) j@106@01)))
  ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) ($Seq.index
    matrix@112@01
    (+ (* i@107@01 step@105@01) j@106@01))))))
 (set-option :rlimit 4613) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(assert (=
  ($FVF.lookup_Ref__Integer_value (as sm@169@01  $FVF<Int>) ($Seq.index
    matrix@112@01
    (+ (* i@107@01 step@105@01) j@106@01)))
  ($FVF.lookup_Ref__Integer_value (as sm@132@01  $FVF<Int>) ($Seq.index
    matrix@112@01
    (+ (* i@107@01 step@105@01) j@106@01)))))
(pop) ; 2
(pop) ; 1
; ---------- Ref__histogram ----------
(declare-const diz@170@01 $Ref)
(declare-const M@171@01 Int)
(declare-const N@172@01 Int)
(declare-const step@173@01 Int)
(declare-const matrix@174@01 $Seq<$Ref>)
(declare-const P@175@01 Int)
(declare-const hist@176@01 $Seq<$Ref>)
(declare-const diz@177@01 $Ref)
(declare-const M@178@01 Int)
(declare-const N@179@01 Int)
(declare-const step@180@01 Int)
(declare-const matrix@181@01 $Seq<$Ref>)
(declare-const P@182@01 Int)
(declare-const hist@183@01 $Seq<$Ref>)
(push) ; 1
(declare-const $t@184@01 $Snap)
(declare-const $t@185@01 $Snap)
(assert (= $t@184@01 ($Snap.combine $Snap.unit $t@185@01)))
; [eval] diz != null
(assert (not (= diz@177@01 $Ref.null)))
(declare-const $t@186@01 $Snap)
(assert (= $t@185@01 ($Snap.combine $Snap.unit $t@186@01)))
; [eval] M > 0
(assert (> M@178@01 0))
(declare-const $t@187@01 $Snap)
(assert (= $t@186@01 ($Snap.combine $Snap.unit $t@187@01)))
; [eval] N > 0
(assert (> N@179@01 0))
(declare-const $t@188@01 $Snap)
(assert (= $t@187@01 ($Snap.combine $Snap.unit $t@188@01)))
; [eval] step >= N
(assert (>= step@180@01 N@179@01))
(declare-const $t@189@01 $Snap)
(assert (= $t@188@01 ($Snap.combine $Snap.unit $t@189@01)))
; [eval] P > 0
(assert (> P@182@01 0))
(declare-const $t@190@01 $Snap)
(assert (= $t@189@01 ($Snap.combine $Snap.unit $t@190@01)))
; [eval] N <= step
(assert (<= N@179@01 step@180@01))
(declare-const $t@191@01 $Snap)
(assert (= $t@190@01 ($Snap.combine $Snap.unit $t@191@01)))
; [eval] M * step <= |matrix|
; [eval] M * step
; [eval] |matrix|
(assert (<= (* M@178@01 step@180@01) ($Seq.length matrix@181@01)))
(declare-const $t@192@01 $FVF<Int>)
(declare-const $t@193@01 $Snap)
(assert (=
  $t@191@01
  ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@192@01) $t@193@01)))
(declare-const j1@194@01 Int)
(push) ; 2
; [eval] (j1 in [0..M * step)) && j1 % step < N
; [eval] (j1 in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@195@01 ==> j1 % step < N
(push) ; 3
; [then-branch: 16 | j1@194@01 in [0..M@178@01 * step@180@01] | live]
; [else-branch: 16 | !j1@194@01 in [0..M@178@01 * step@180@01] | live]
(push) ; 4
; [then-branch: 16 | j1@194@01 in [0..M@178@01 * step@180@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@194@01))
; [eval] j1 % step < N
; [eval] j1 % step
(push) ; 5
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 16705) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(pop) ; 4
(push) ; 4
; [else-branch: 16 | !j1@194@01 in [0..M@178@01 * step@180@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@194@01)))
(pop) ; 4
(pop) ; 3
; Joined path conditions
; Joined path conditions
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@194@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@194@01)
    (< (mod j1@194@01 step@180@01) N@179@01))))
; [eval] matrix[j1]
(push) ; 3
(assert (not (>= j1@194@01 0)))
 (set-option :rlimit 14922) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (< j1@194@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 334) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (not (= 2 0))))
 (set-option :rlimit 99945) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(pop) ; 2
(declare-fun inv@196@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((j1@194@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@194@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@194@01)
        (< (mod j1@194@01 step@180@01) N@179@01)))
    (= (inv@196@01 ($Seq.index matrix@181@01 j1@194@01)) j1@194@01))
  :pattern (($Seq.index matrix@181@01 j1@194@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (< (mod (inv@196@01 r) step@180@01) N@179@01)))
    (= ($Seq.index matrix@181@01 (inv@196@01 r)) r))
  :pattern ((inv@196@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j1@194@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@194@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@194@01)
        (< (mod j1@194@01 step@180@01) N@179@01)))
    (not (= ($Seq.index matrix@181@01 j1@194@01) $Ref.null)))
  :pattern (($Seq.index matrix@181@01 j1@194@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
(declare-const $t@197@01 $Snap)
(assert (= $t@193@01 ($Snap.combine $Snap.unit $t@197@01)))
; [eval] N <= step
(declare-const $t@198@01 $Snap)
(assert (= $t@197@01 ($Snap.combine $Snap.unit $t@198@01)))
; [eval] (forall k_fresh_rw_0: Int :: { matrix[k_fresh_rw_0] } (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> (matrix[k_fresh_rw_0].Ref__Integer_value in [0..P)))
(declare-const k_fresh_rw_0@199@01 Int)
(push) ; 2
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> (matrix[k_fresh_rw_0].Ref__Integer_value in [0..P))
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N
; [eval] (k_fresh_rw_0 in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@200@01 ==> k_fresh_rw_0 % step < N
(push) ; 3
; [then-branch: 17 | k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01] | live]
; [else-branch: 17 | !k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01] | live]
(push) ; 4
; [then-branch: 17 | k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@199@01))
; [eval] k_fresh_rw_0 % step < N
; [eval] k_fresh_rw_0 % step
(push) ; 5
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 66119) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(pop) ; 4
(push) ; 4
; [else-branch: 17 | !k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@199@01)))
(pop) ; 4
(pop) ; 3
; Joined path conditions
; Joined path conditions
(push) ; 3
; [then-branch: 18 | k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@199@01 % step@180@01 < N@179@01 | live]
; [else-branch: 18 | !k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@199@01 % step@180@01 < N@179@01 | live]
(push) ; 4
; [then-branch: 18 | k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@199@01 % step@180@01 < N@179@01]
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@199@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@199@01)
    (< (mod k_fresh_rw_0@199@01 step@180@01) N@179@01))))
; [eval] (matrix[k_fresh_rw_0].Ref__Integer_value in [0..P))
; [eval] [0..P)
; [eval] matrix[k_fresh_rw_0]
(push) ; 5
(assert (not (>= k_fresh_rw_0@199@01 0)))
 (set-option :rlimit 24804) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(push) ; 5
(assert (not (< k_fresh_rw_0@199@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 80846) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(push) ; 5
(assert (not (and
  ($Seq.contains
    ($Seq.range 0 (* M@178@01 step@180@01))
    (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@199@01)))
  (implies
    ($Seq.contains
      ($Seq.range 0 (* M@178@01 step@180@01))
      (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@199@01)))
    (<
      (mod
        (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@199@01))
        step@180@01)
      N@179@01)))))
 (set-option :rlimit 6577) (check-sat) 
; unsat
(pop) ; 5
; 0.00s
; 
(declare-const sm@201@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@201@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@201@01  $FVF<Int>) r))
    :qid |qp.fvfValDef22|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@201@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef22|))))
(pop) ; 4
(push) ; 4
; [else-branch: 18 | !k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@199@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@199@01 % step@180@01 < N@179@01]
(assert (not
  (and
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@199@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@199@01)
      (< (mod k_fresh_rw_0@199@01 step@180@01) N@179@01)))))
(pop) ; 4
(pop) ; 3
; Joined path conditions
(assert (implies
  (and
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@199@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@199@01)
      (< (mod k_fresh_rw_0@199@01 step@180@01) N@179@01)))
  (and
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@201@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@201@01  $FVF<Int>) r))
        :qid |qp.fvfValDef22|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@201@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
        :qid |qp.fvfValDef22|)))
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@199@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@199@01)
        (< (mod k_fresh_rw_0@199@01 step@180@01) N@179@01))))))
; Joined path conditions
(pop) ; 2
; Nested auxiliary terms
(assert (forall ((k_fresh_rw_0@199@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@199@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@199@01)
        (< (mod k_fresh_rw_0@199@01 step@180@01) N@179@01)))
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@201@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@201@01  $FVF<Int>) r))
          :qid |qp.fvfValDef22|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@201@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef22|)))
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@199@01)
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            k_fresh_rw_0@199@01)
          (< (mod k_fresh_rw_0@199@01 step@180@01) N@179@01)))))
  :pattern (($Seq.index matrix@181@01 k_fresh_rw_0@199@01))
  :qid |prog.l131-aux|)))
(assert (forall ((k_fresh_rw_0@199@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@199@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@199@01)
        (< (mod k_fresh_rw_0@199@01 step@180@01) N@179@01)))
    ($Seq.contains
      ($Seq.range 0 P@182@01)
      ($FVF.lookup_Ref__Integer_value (as sm@201@01  $FVF<Int>) ($Seq.index
        matrix@181@01
        k_fresh_rw_0@199@01))))
  :pattern (($Seq.index matrix@181@01 k_fresh_rw_0@199@01))
  :qid |prog.l131|)))
(declare-const $t@202@01 $FVF<Int>)
(assert (=
  $t@198@01
  ($Snap.combine $Snap.unit ($SortWrappers.$FVF<Int>To$Snap $t@202@01))))
; [eval] P <= |hist|
; [eval] |hist|
(assert (<= P@182@01 ($Seq.length hist@183@01)))
(declare-const i1@203@01 Int)
(push) ; 2
; [eval] (i1 in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@182@01) i1@203@01))
; [eval] hist[i1]
(push) ; 3
(assert (not (>= i1@203@01 0)))
 (set-option :rlimit 21477) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(push) ; 3
(assert (not (< i1@203@01 ($Seq.length hist@183@01))))
 (set-option :rlimit 1110285) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
(pop) ; 2
(declare-fun inv@204@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((i1@203@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) i1@203@01)
    (= (inv@204@01 ($Seq.index hist@183@01 i1@203@01)) i1@203@01))
  :pattern (($Seq.index hist@183@01 i1@203@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@204@01 r))
    (= ($Seq.index hist@183@01 (inv@204@01 r)) r))
  :pattern ((inv@204@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((i1@203@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) i1@203@01)
    (not (= ($Seq.index hist@183@01 i1@203@01) $Ref.null)))
  :pattern (($Seq.index hist@183@01 i1@203@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
; State saturation: after contract
;(set-option :timeout 50)
 (set-option :rlimit 15829) (check-sat) 
; unknown
(push) ; 2
(declare-const $t@205@01 $Snap)
(declare-const $t@206@01 $Snap)
(assert (= $t@205@01 ($Snap.combine $Snap.unit $t@206@01)))
; [eval] M > 0
(declare-const $t@207@01 $Snap)
(assert (= $t@206@01 ($Snap.combine $Snap.unit $t@207@01)))
; [eval] N > 0
(declare-const $t@208@01 $Snap)
(assert (= $t@207@01 ($Snap.combine $Snap.unit $t@208@01)))
; [eval] step >= N
(declare-const $t@209@01 $Snap)
(assert (= $t@208@01 ($Snap.combine $Snap.unit $t@209@01)))
; [eval] P > 0
(declare-const $t@210@01 $Snap)
(assert (= $t@209@01 ($Snap.combine $Snap.unit $t@210@01)))
; [eval] N <= step
(declare-const $t@211@01 $FVF<Int>)
(declare-const $t@212@01 $Snap)
(assert (=
  $t@210@01
  ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@211@01) $t@212@01)))
(declare-const j1@213@01 Int)
(push) ; 3
; [eval] (j1 in [0..M * step)) && j1 % step < N
; [eval] (j1 in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@214@01 ==> j1 % step < N
(push) ; 4
; [then-branch: 19 | j1@213@01 in [0..M@178@01 * step@180@01] | live]
; [else-branch: 19 | !j1@213@01 in [0..M@178@01 * step@180@01] | live]
(push) ; 5
; [then-branch: 19 | j1@213@01 in [0..M@178@01 * step@180@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@213@01))
; [eval] j1 % step < N
; [eval] j1 % step
;(set-option :timeout 0)
(push) ; 6
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 39314) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(pop) ; 5
(push) ; 5
; [else-branch: 19 | !j1@213@01 in [0..M@178@01 * step@180@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@213@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@213@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@213@01)
    (< (mod j1@213@01 step@180@01) N@179@01))))
; [eval] matrix[j1]
(push) ; 4
(assert (not (>= j1@213@01 0)))
 (set-option :rlimit 8539) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< j1@213@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 157476) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (not (= 2 0))))
 (set-option :rlimit 211940) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@215@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((j1@213@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@213@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@213@01)
        (< (mod j1@213@01 step@180@01) N@179@01)))
    (= (inv@215@01 ($Seq.index matrix@181@01 j1@213@01)) j1@213@01))
  :pattern (($Seq.index matrix@181@01 j1@213@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
        (< (mod (inv@215@01 r) step@180@01) N@179@01)))
    (= ($Seq.index matrix@181@01 (inv@215@01 r)) r))
  :pattern ((inv@215@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j1@213@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@213@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@213@01)
        (< (mod j1@213@01 step@180@01) N@179@01)))
    (not (= ($Seq.index matrix@181@01 j1@213@01) $Ref.null)))
  :pattern (($Seq.index matrix@181@01 j1@213@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
(declare-const $t@216@01 $FVF<Int>)
(assert (=
  $t@212@01
  ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@216@01) $Snap.unit)))
(declare-const i1@217@01 Int)
(push) ; 3
; [eval] (i1 in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@182@01) i1@217@01))
; [eval] hist[i1]
(push) ; 4
(assert (not (>= i1@217@01 0)))
 (set-option :rlimit 58593) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< i1@217@01 ($Seq.length hist@183@01))))
 (set-option :rlimit 297524) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@218@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((i1@217@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) i1@217@01)
    (= (inv@218@01 ($Seq.index hist@183@01 i1@217@01)) i1@217@01))
  :pattern (($Seq.index hist@183@01 i1@217@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
    (= ($Seq.index hist@183@01 (inv@218@01 r)) r))
  :pattern ((inv@218@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((i1@217@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) i1@217@01)
    (not (= ($Seq.index hist@183@01 i1@217@01) $Ref.null)))
  :pattern (($Seq.index hist@183@01 i1@217@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
; [eval] (forall k: Int :: { (k in [0..P)) } { hist[k] } (k in [0..P)) ==> hist[k].Ref__Integer_value == count_square(0, 0, N, step, 0, M * step, matrix, k))
(declare-const k@219@01 Int)
(push) ; 3
; [eval] (k in [0..P)) ==> hist[k].Ref__Integer_value == count_square(0, 0, N, step, 0, M * step, matrix, k)
; [eval] (k in [0..P))
; [eval] [0..P)
(push) ; 4
; [then-branch: 20 | k@219@01 in [0..P@182@01] | live]
; [else-branch: 20 | !k@219@01 in [0..P@182@01] | live]
(push) ; 5
; [then-branch: 20 | k@219@01 in [0..P@182@01]]
(assert ($Seq.contains ($Seq.range 0 P@182@01) k@219@01))
; [eval] hist[k].Ref__Integer_value == count_square(0, 0, N, step, 0, M * step, matrix, k)
; [eval] hist[k]
(push) ; 6
(assert (not (>= k@219@01 0)))
 (set-option :rlimit 15360) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k@219@01 ($Seq.length hist@183@01))))
 (set-option :rlimit 19975) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@182@01)
        (inv@218@01 ($Seq.index hist@183@01 k@219@01)))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          (inv@215@01 ($Seq.index hist@183@01 k@219@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            (inv@215@01 ($Seq.index hist@183@01 k@219@01)))
          (<
            (mod (inv@215@01 ($Seq.index hist@183@01 k@219@01)) step@180@01)
            N@179@01)))
      (/ (to_real 1) (to_real 2))
      $Perm.No)))))
 (set-option :rlimit 89146) (check-sat) 
; unsat
(pop) ; 6
; 0.01s
; 
(declare-const sm@220@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
    :qid |qp.fvfValDef23|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
    :qid |qp.fvfValDef23|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
          (< (mod (inv@215@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
    :qid |qp.fvfValDef24|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
          (< (mod (inv@215@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
    :qid |qp.fvfValDef24|))))
; [eval] count_square(0, 0, N, step, 0, M * step, matrix, k)
; [eval] M * step
(push) ; 6
; [eval] 0 <= 0
; [eval] 0 <= N
(push) ; 7
(assert (not (<= 0 N@179@01)))
 (set-option :rlimit 25755) (check-sat) 
; unsat
(pop) ; 7
; 0.00s
; 
(assert (<= 0 N@179@01))
; [eval] N <= step
; [eval] step > 0
(push) ; 7
(assert (not (> step@180@01 0)))
 (set-option :rlimit 60712) (check-sat) 
; unsat
(pop) ; 7
; 0.00s
; 
(assert (> step@180@01 0))
; [eval] 0 <= 0
; [eval] 0 <= 0
; [eval] 0 <= M * step
; [eval] M * step
(push) ; 7
(assert (not (<= 0 (* M@178@01 step@180@01))))
 (set-option :rlimit 98224) (check-sat) 
; unsat
(pop) ; 7
; 0.01s
; 
(assert (<= 0 (* M@178@01 step@180@01)))
; [eval] M * step <= |matrix|
; [eval] M * step
; [eval] |matrix|
(declare-const k@221@01 Int)
(push) ; 7
; [eval] 0 <= k && (k < M * step && (0 <= k % step && k % step < N))
; [eval] 0 <= k
; [eval] v@222@01 ==> k < M * step && (0 <= k % step && k % step < N)
(push) ; 8
; [then-branch: 21 | 0 <= k@221@01 | live]
; [else-branch: 21 | !0 <= k@221@01 | live]
(push) ; 9
; [then-branch: 21 | 0 <= k@221@01]
(assert (<= 0 k@221@01))
; [eval] k < M * step && (0 <= k % step && k % step < N)
; [eval] k < M * step
; [eval] M * step
; [eval] v@223@01 ==> 0 <= k % step && k % step < N
(push) ; 10
; [then-branch: 22 | k@221@01 < M@178@01 * step@180@01 | live]
; [else-branch: 22 | !k@221@01 < M@178@01 * step@180@01 | live]
(push) ; 11
; [then-branch: 22 | k@221@01 < M@178@01 * step@180@01]
(assert (< k@221@01 (* M@178@01 step@180@01)))
; [eval] 0 <= k % step && k % step < N
; [eval] 0 <= k % step
; [eval] k % step
(push) ; 12
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 88161) (check-sat) 
; unsat
(pop) ; 12
; 0.00s
; 
; [eval] v@224@01 ==> k % step < N
(push) ; 12
; [then-branch: 23 | 0 <= k@221@01 % step@180@01 | live]
; [else-branch: 23 | !0 <= k@221@01 % step@180@01 | live]
(push) ; 13
; [then-branch: 23 | 0 <= k@221@01 % step@180@01]
(assert (<= 0 (mod k@221@01 step@180@01)))
; [eval] k % step < N
; [eval] k % step
(push) ; 14
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 4314) (check-sat) 
; unsat
(pop) ; 14
; 0.00s
; 
(pop) ; 13
(push) ; 13
; [else-branch: 23 | !0 <= k@221@01 % step@180@01]
(assert (not (<= 0 (mod k@221@01 step@180@01))))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
(pop) ; 11
(push) ; 11
; [else-branch: 22 | !k@221@01 < M@178@01 * step@180@01]
(assert (not (< k@221@01 (* M@178@01 step@180@01))))
(pop) ; 11
(pop) ; 10
; Joined path conditions
; Joined path conditions
(pop) ; 9
(push) ; 9
; [else-branch: 21 | !0 <= k@221@01]
(assert (not (<= 0 k@221@01)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (and
  (<= 0 k@221@01)
  (implies
    (<= 0 k@221@01)
    (and
      (< k@221@01 (* M@178@01 step@180@01))
      (implies
        (< k@221@01 (* M@178@01 step@180@01))
        (and
          (<= 0 (mod k@221@01 step@180@01))
          (implies
            (<= 0 (mod k@221@01 step@180@01))
            (< (mod k@221@01 step@180@01) N@179@01))))))))
(declare-const $k@225@01 $Perm)
(assert ($Perm.isReadVar $k@225@01 $Perm.Write))
; [eval] matrix[k]
(push) ; 8
(assert (not (>= k@221@01 0)))
 (set-option :rlimit 19867) (check-sat) 
; unsat
(pop) ; 8
; 0.00s
; 
(push) ; 8
(assert (not (< k@221@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 194625) (check-sat) 
; unsat
(pop) ; 8
; 0.00s
; 
(pop) ; 7
(declare-fun inv@226@01 ($Ref) Int)
; Nested auxiliary terms
(assert (forall ((k@221@01 Int)) (!
  ($Perm.isReadVar $k@225@01 $Perm.Write)
  :pattern (($Seq.index matrix@181@01 k@221@01))
  :qid |Ref__Integer_value-aux|)))
(push) ; 7
(assert (not (forall ((k@221@01 Int)) (!
  (implies
    (and
      (<= 0 k@221@01)
      (implies
        (<= 0 k@221@01)
        (and
          (< k@221@01 (* M@178@01 step@180@01))
          (implies
            (< k@221@01 (* M@178@01 step@180@01))
            (and
              (<= 0 (mod k@221@01 step@180@01))
              (implies
                (<= 0 (mod k@221@01 step@180@01))
                (< (mod k@221@01 step@180@01) N@179@01)))))))
    (or (= $k@225@01 $Perm.No) (< $Perm.No $k@225@01)))
  
  ))))
 (set-option :rlimit 2889) (check-sat) 
; unsat
(pop) ; 7
; 0.00s
; 
; Check receiver injectivity
(push) ; 7
(assert (not (forall ((k1@221@01 Int) (k2@221@01 Int)) (!
  (implies
    (and
      (and
        (and
          (<= 0 k1@221@01)
          (implies
            (<= 0 k1@221@01)
            (and
              (< k1@221@01 (* M@178@01 step@180@01))
              (implies
                (< k1@221@01 (* M@178@01 step@180@01))
                (and
                  (<= 0 (mod k1@221@01 step@180@01))
                  (implies
                    (<= 0 (mod k1@221@01 step@180@01))
                    (< (mod k1@221@01 step@180@01) N@179@01)))))))
        (< $Perm.No $k@225@01))
      (and
        (and
          (<= 0 k2@221@01)
          (implies
            (<= 0 k2@221@01)
            (and
              (< k2@221@01 (* M@178@01 step@180@01))
              (implies
                (< k2@221@01 (* M@178@01 step@180@01))
                (and
                  (<= 0 (mod k2@221@01 step@180@01))
                  (implies
                    (<= 0 (mod k2@221@01 step@180@01))
                    (< (mod k2@221@01 step@180@01) N@179@01)))))))
        (< $Perm.No $k@225@01))
      (=
        ($Seq.index matrix@181@01 k1@221@01)
        ($Seq.index matrix@181@01 k2@221@01)))
    (= k1@221@01 k2@221@01))
  
  :qid |Ref__Integer_value-rcvrInj|))))
 (set-option :rlimit 9770) (check-sat) 
; unsat
(pop) ; 7
; 0.02s
; 
; Definitional axioms for inverse functions
(assert (forall ((k@221@01 Int)) (!
  (implies
    (and
      (and
        (<= 0 k@221@01)
        (implies
          (<= 0 k@221@01)
          (and
            (< k@221@01 (* M@178@01 step@180@01))
            (implies
              (< k@221@01 (* M@178@01 step@180@01))
              (and
                (<= 0 (mod k@221@01 step@180@01))
                (implies
                  (<= 0 (mod k@221@01 step@180@01))
                  (< (mod k@221@01 step@180@01) N@179@01)))))))
      (< $Perm.No $k@225@01))
    (= (inv@226@01 ($Seq.index matrix@181@01 k@221@01)) k@221@01))
  :pattern (($Seq.index matrix@181@01 k@221@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    (and
      (and
        (<= 0 (inv@226@01 r))
        (implies
          (<= 0 (inv@226@01 r))
          (and
            (< (inv@226@01 r) (* M@178@01 step@180@01))
            (implies
              (< (inv@226@01 r) (* M@178@01 step@180@01))
              (and
                (<= 0 (mod (inv@226@01 r) step@180@01))
                (implies
                  (<= 0 (mod (inv@226@01 r) step@180@01))
                  (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
      (< $Perm.No $k@225@01))
    (= ($Seq.index matrix@181@01 (inv@226@01 r)) r))
  :pattern ((inv@226@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@227@01 ((r $Ref)) $Perm
  (ite
    (and
      (<= 0 (inv@226@01 r))
      (implies
        (<= 0 (inv@226@01 r))
        (and
          (< (inv@226@01 r) (* M@178@01 step@180@01))
          (implies
            (< (inv@226@01 r) (* M@178@01 step@180@01))
            (and
              (<= 0 (mod (inv@226@01 r) step@180@01))
              (implies
                (<= 0 (mod (inv@226@01 r) step@180@01))
                (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
    ($Perm.min
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (< (mod (inv@215@01 r) step@180@01) N@179@01)))
        (/ (to_real 1) (to_real 2))
        $Perm.No)
      $k@225@01)
    $Perm.No))
(define-fun pTaken@228@01 ((r $Ref)) $Perm
  (ite
    (and
      (<= 0 (inv@226@01 r))
      (implies
        (<= 0 (inv@226@01 r))
        (and
          (< (inv@226@01 r) (* M@178@01 step@180@01))
          (implies
            (< (inv@226@01 r) (* M@178@01 step@180@01))
            (and
              (<= 0 (mod (inv@226@01 r) step@180@01))
              (implies
                (<= 0 (mod (inv@226@01 r) step@180@01))
                (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
    ($Perm.min
      (ite
        ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
        $Perm.Write
        $Perm.No)
      (- $k@225@01 (pTaken@227@01 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
;(set-option :timeout 10)
 (set-option :rlimit 23549) (check-sat) 
; unknown
; Constrain original permissions $k@225@01
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (not
        (=
          (ite
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (< (mod (inv@215@01 r) step@180@01) N@179@01)))
            (/ (to_real 1) (to_real 2))
            $Perm.No)
          $Perm.No))
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (< (mod (inv@215@01 r) step@180@01) N@179@01)))
        (<
          (ite
            (and
              (<= 0 (inv@226@01 r))
              (implies
                (<= 0 (inv@226@01 r))
                (and
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
            $k@225@01
            $Perm.No)
          (/ (to_real 1) (to_real 2)))
        (<
          (ite
            (and
              (<= 0 (inv@226@01 r))
              (implies
                (<= 0 (inv@226@01 r))
                (and
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
            $k@225@01
            $Perm.No)
          $Perm.No)))
    :pattern ((inv@215@01 r))
    :qid |qp.srp25|))
  (forall ((r $Ref)) (!
    (implies
      (not
        (=
          (ite
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (< (mod (inv@215@01 r) step@180@01) N@179@01)))
            (/ (to_real 1) (to_real 2))
            $Perm.No)
          $Perm.No))
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (< (mod (inv@215@01 r) step@180@01) N@179@01)))
        (<
          (ite
            (and
              (<= 0 (inv@226@01 r))
              (implies
                (<= 0 (inv@226@01 r))
                (and
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
            $k@225@01
            $Perm.No)
          (/ (to_real 1) (to_real 2)))
        (<
          (ite
            (and
              (<= 0 (inv@226@01 r))
              (implies
                (<= 0 (inv@226@01 r))
                (and
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
            $k@225@01
            $Perm.No)
          $Perm.No)))
    :pattern ((inv@226@01 r))
    :qid |qp.srp25|))))
; Intermediate check if already taken enough permissions
;(set-option :timeout 500)
(push) ; 7
(assert (not (forall ((r $Ref)) (!
  (implies
    (and
      (<= 0 (inv@226@01 r))
      (implies
        (<= 0 (inv@226@01 r))
        (and
          (< (inv@226@01 r) (* M@178@01 step@180@01))
          (implies
            (< (inv@226@01 r) (* M@178@01 step@180@01))
            (and
              (<= 0 (mod (inv@226@01 r) step@180@01))
              (implies
                (<= 0 (mod (inv@226@01 r) step@180@01))
                (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
    (= (- $k@225@01 (pTaken@227@01 r)) $Perm.No))
  
  ))))
 (set-option :rlimit 55413) (check-sat) 
; unsat
(pop) ; 7
; 0.03s
; 
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@229@01 $FVF<Int>)
; Definitional axioms for SM domain
(assert (forall ((r $Ref)) (!
  (iff
    (Set_in r ($FVF.domain_Ref__Integer_value (as sm@229@01  $FVF<Int>)))
    (and
      (and
        (<= 0 (inv@226@01 r))
        (implies
          (<= 0 (inv@226@01 r))
          (and
            (< (inv@226@01 r) (* M@178@01 step@180@01))
            (implies
              (< (inv@226@01 r) (* M@178@01 step@180@01))
              (and
                (<= 0 (mod (inv@226@01 r) step@180@01))
                (implies
                  (<= 0 (mod (inv@226@01 r) step@180@01))
                  (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
      (< $Perm.No $k@225@01)))
  :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@229@01  $FVF<Int>))))
  :qid |qp.fvfDomDef28|)))
; Definitional axioms for SM values
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@226@01 r))
            (implies
              (<= 0 (inv@226@01 r))
              (and
                (< (inv@226@01 r) (* M@178@01 step@180@01))
                (implies
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (and
                    (<= 0 (mod (inv@226@01 r) step@180@01))
                    (implies
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
          (< $Perm.No $k@225@01))
        ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r))
    :qid |qp.fvfValDef26|))
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@226@01 r))
            (implies
              (<= 0 (inv@226@01 r))
              (and
                (< (inv@226@01 r) (* M@178@01 step@180@01))
                (implies
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (and
                    (<= 0 (mod (inv@226@01 r) step@180@01))
                    (implies
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
          (< $Perm.No $k@225@01))
        ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
    :qid |qp.fvfValDef26|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@226@01 r))
            (implies
              (<= 0 (inv@226@01 r))
              (and
                (< (inv@226@01 r) (* M@178@01 step@180@01))
                (implies
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (and
                    (<= 0 (mod (inv@226@01 r) step@180@01))
                    (implies
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
          (< $Perm.No $k@225@01))
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (< (mod (inv@215@01 r) step@180@01) N@179@01))))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r))
    :qid |qp.fvfValDef27|))
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@226@01 r))
            (implies
              (<= 0 (inv@226@01 r))
              (and
                (< (inv@226@01 r) (* M@178@01 step@180@01))
                (implies
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (and
                    (<= 0 (mod (inv@226@01 r) step@180@01))
                    (implies
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
          (< $Perm.No $k@225@01))
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (< (mod (inv@215@01 r) step@180@01) N@179@01))))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
    :qid |qp.fvfValDef27|))))
(pop) ; 6
; Joined path conditions
(assert (and
  (and
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@226@01 r))
              (implies
                (<= 0 (inv@226@01 r))
                (and
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@225@01))
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (< (mod (inv@215@01 r) step@180@01) N@179@01))))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r))
      :qid |qp.fvfValDef27|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@226@01 r))
              (implies
                (<= 0 (inv@226@01 r))
                (and
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@225@01))
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (< (mod (inv@215@01 r) step@180@01) N@179@01))))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
      :qid |qp.fvfValDef27|)))
  (and
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@226@01 r))
              (implies
                (<= 0 (inv@226@01 r))
                (and
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@225@01))
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r)))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r))
      :qid |qp.fvfValDef26|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@226@01 r))
              (implies
                (<= 0 (inv@226@01 r))
                (and
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@225@01))
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r)))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
      :qid |qp.fvfValDef26|)))
  (forall ((r $Ref)) (!
    (iff
      (Set_in r ($FVF.domain_Ref__Integer_value (as sm@229@01  $FVF<Int>)))
      (and
        (and
          (<= 0 (inv@226@01 r))
          (implies
            (<= 0 (inv@226@01 r))
            (and
              (< (inv@226@01 r) (* M@178@01 step@180@01))
              (implies
                (< (inv@226@01 r) (* M@178@01 step@180@01))
                (and
                  (<= 0 (mod (inv@226@01 r) step@180@01))
                  (implies
                    (<= 0 (mod (inv@226@01 r) step@180@01))
                    (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
        (< $Perm.No $k@225@01)))
    :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@229@01  $FVF<Int>))))
    :qid |qp.fvfDomDef28|))
  (and
    (forall ((r $Ref)) (!
      (implies
        (not
          (=
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (< (mod (inv@215@01 r) step@180@01) N@179@01)))
              (/ (to_real 1) (to_real 2))
              $Perm.No)
            $Perm.No))
        (ite
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (< (mod (inv@215@01 r) step@180@01) N@179@01)))
          (<
            (ite
              (and
                (<= 0 (inv@226@01 r))
                (implies
                  (<= 0 (inv@226@01 r))
                  (and
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
              $k@225@01
              $Perm.No)
            (/ (to_real 1) (to_real 2)))
          (<
            (ite
              (and
                (<= 0 (inv@226@01 r))
                (implies
                  (<= 0 (inv@226@01 r))
                  (and
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
              $k@225@01
              $Perm.No)
            $Perm.No)))
      :pattern ((inv@215@01 r))
      :qid |qp.srp25|))
    (forall ((r $Ref)) (!
      (implies
        (not
          (=
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (< (mod (inv@215@01 r) step@180@01) N@179@01)))
              (/ (to_real 1) (to_real 2))
              $Perm.No)
            $Perm.No))
        (ite
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (< (mod (inv@215@01 r) step@180@01) N@179@01)))
          (<
            (ite
              (and
                (<= 0 (inv@226@01 r))
                (implies
                  (<= 0 (inv@226@01 r))
                  (and
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
              $k@225@01
              $Perm.No)
            (/ (to_real 1) (to_real 2)))
          (<
            (ite
              (and
                (<= 0 (inv@226@01 r))
                (implies
                  (<= 0 (inv@226@01 r))
                  (and
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
              $k@225@01
              $Perm.No)
            $Perm.No)))
      :pattern ((inv@226@01 r))
      :qid |qp.srp25|)))
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (<= 0 (inv@226@01 r))
          (implies
            (<= 0 (inv@226@01 r))
            (and
              (< (inv@226@01 r) (* M@178@01 step@180@01))
              (implies
                (< (inv@226@01 r) (* M@178@01 step@180@01))
                (and
                  (<= 0 (mod (inv@226@01 r) step@180@01))
                  (implies
                    (<= 0 (mod (inv@226@01 r) step@180@01))
                    (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
        (< $Perm.No $k@225@01))
      (= ($Seq.index matrix@181@01 (inv@226@01 r)) r))
    :pattern ((inv@226@01 r))
    :qid |Ref__Integer_value-fctOfInv|))
  (forall ((k@221@01 Int)) (!
    (implies
      (and
        (and
          (<= 0 k@221@01)
          (implies
            (<= 0 k@221@01)
            (and
              (< k@221@01 (* M@178@01 step@180@01))
              (implies
                (< k@221@01 (* M@178@01 step@180@01))
                (and
                  (<= 0 (mod k@221@01 step@180@01))
                  (implies
                    (<= 0 (mod k@221@01 step@180@01))
                    (< (mod k@221@01 step@180@01) N@179@01)))))))
        (< $Perm.No $k@225@01))
      (= (inv@226@01 ($Seq.index matrix@181@01 k@221@01)) k@221@01))
    :pattern (($Seq.index matrix@181@01 k@221@01))
    :qid |Ref__Integer_value-invOfFct|))
  (forall ((k@221@01 Int)) (!
    ($Perm.isReadVar $k@225@01 $Perm.Write)
    :pattern (($Seq.index matrix@181@01 k@221@01))
    :qid |Ref__Integer_value-aux|))
  (<= 0 (* M@178@01 step@180@01))
  (> step@180@01 0)
  (<= 0 N@179@01)))
(pop) ; 5
(push) ; 5
; [else-branch: 20 | !k@219@01 in [0..P@182@01]]
(assert (not ($Seq.contains ($Seq.range 0 P@182@01) k@219@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (implies
  ($Seq.contains ($Seq.range 0 P@182@01) k@219@01)
  (and
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@226@01 r))
                  (implies
                    (<= 0 (inv@226@01 r))
                    (and
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (implies
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (and
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (implies
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                (< $Perm.No $k@225@01))
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (< (mod (inv@215@01 r) step@180@01) N@179@01))))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r))
          :qid |qp.fvfValDef27|))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@226@01 r))
                  (implies
                    (<= 0 (inv@226@01 r))
                    (and
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (implies
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (and
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (implies
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                (< $Perm.No $k@225@01))
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (< (mod (inv@215@01 r) step@180@01) N@179@01))))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
          :qid |qp.fvfValDef27|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@226@01 r))
                  (implies
                    (<= 0 (inv@226@01 r))
                    (and
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (implies
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (and
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (implies
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                (< $Perm.No $k@225@01))
              ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r))
          :qid |qp.fvfValDef26|))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@226@01 r))
                  (implies
                    (<= 0 (inv@226@01 r))
                    (and
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (implies
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (and
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (implies
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                (< $Perm.No $k@225@01))
              ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
          :qid |qp.fvfValDef26|)))
      (forall ((r $Ref)) (!
        (iff
          (Set_in r ($FVF.domain_Ref__Integer_value (as sm@229@01  $FVF<Int>)))
          (and
            (and
              (<= 0 (inv@226@01 r))
              (implies
                (<= 0 (inv@226@01 r))
                (and
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@225@01)))
        :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@229@01  $FVF<Int>))))
        :qid |qp.fvfDomDef28|))
      (and
        (forall ((r $Ref)) (!
          (implies
            (not
              (=
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@215@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@215@01 r))
                      (< (mod (inv@215@01 r) step@180@01) N@179@01)))
                  (/ (to_real 1) (to_real 2))
                  $Perm.No)
                $Perm.No))
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (< (mod (inv@215@01 r) step@180@01) N@179@01)))
              (<
                (ite
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  $k@225@01
                  $Perm.No)
                (/ (to_real 1) (to_real 2)))
              (<
                (ite
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  $k@225@01
                  $Perm.No)
                $Perm.No)))
          :pattern ((inv@215@01 r))
          :qid |qp.srp25|))
        (forall ((r $Ref)) (!
          (implies
            (not
              (=
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@215@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@215@01 r))
                      (< (mod (inv@215@01 r) step@180@01) N@179@01)))
                  (/ (to_real 1) (to_real 2))
                  $Perm.No)
                $Perm.No))
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (< (mod (inv@215@01 r) step@180@01) N@179@01)))
              (<
                (ite
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  $k@225@01
                  $Perm.No)
                (/ (to_real 1) (to_real 2)))
              (<
                (ite
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  $k@225@01
                  $Perm.No)
                $Perm.No)))
          :pattern ((inv@226@01 r))
          :qid |qp.srp25|)))
      (forall ((r $Ref)) (!
        (implies
          (and
            (and
              (<= 0 (inv@226@01 r))
              (implies
                (<= 0 (inv@226@01 r))
                (and
                  (< (inv@226@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@226@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@225@01))
          (= ($Seq.index matrix@181@01 (inv@226@01 r)) r))
        :pattern ((inv@226@01 r))
        :qid |Ref__Integer_value-fctOfInv|))
      (forall ((k@221@01 Int)) (!
        (implies
          (and
            (and
              (<= 0 k@221@01)
              (implies
                (<= 0 k@221@01)
                (and
                  (< k@221@01 (* M@178@01 step@180@01))
                  (implies
                    (< k@221@01 (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod k@221@01 step@180@01))
                      (implies
                        (<= 0 (mod k@221@01 step@180@01))
                        (< (mod k@221@01 step@180@01) N@179@01)))))))
            (< $Perm.No $k@225@01))
          (= (inv@226@01 ($Seq.index matrix@181@01 k@221@01)) k@221@01))
        :pattern (($Seq.index matrix@181@01 k@221@01))
        :qid |Ref__Integer_value-invOfFct|))
      (forall ((k@221@01 Int)) (!
        ($Perm.isReadVar $k@225@01 $Perm.Write)
        :pattern (($Seq.index matrix@181@01 k@221@01))
        :qid |Ref__Integer_value-aux|))
      (<= 0 (* M@178@01 step@180@01))
      (> step@180@01 0)
      (<= 0 N@179@01))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (< (mod (inv@215@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
        :qid |qp.fvfValDef24|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (< (mod (inv@215@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
        :qid |qp.fvfValDef24|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
        :qid |qp.fvfValDef23|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
        :qid |qp.fvfValDef23|)))
    ($Seq.contains ($Seq.range 0 P@182@01) k@219@01))))
; Joined path conditions
; [eval] hist[k]
;(set-option :timeout 0)
(push) ; 4
(assert (not (>= k@219@01 0)))
 (set-option :rlimit 141406) (check-sat) 
; unknown
(pop) ; 4
; 0.01s
; 
(pop) ; 3
; Nested auxiliary terms
(assert (forall ((k@219@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@219@01)
    (and
      (and
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@225@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@215@01 r))
                    (< (mod (inv@215@01 r) step@180@01) N@179@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r))
            :qid |qp.fvfValDef27|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@225@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@215@01 r))
                    (< (mod (inv@215@01 r) step@180@01) N@179@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
            :qid |qp.fvfValDef27|)))
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@225@01))
                ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r))
            :qid |qp.fvfValDef26|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@225@01))
                ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
            :qid |qp.fvfValDef26|)))
        (forall ((r $Ref)) (!
          (iff
            (Set_in r ($FVF.domain_Ref__Integer_value (as sm@229@01  $FVF<Int>)))
            (and
              (and
                (<= 0 (inv@226@01 r))
                (implies
                  (<= 0 (inv@226@01 r))
                  (and
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
              (< $Perm.No $k@225@01)))
          :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@229@01  $FVF<Int>))))
          :qid |qp.fvfDomDef28|))
        (and
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@215@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@215@01 r))
                        (< (mod (inv@215@01 r) step@180@01) N@179@01)))
                    (/ (to_real 1) (to_real 2))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@215@01 r))
                    (< (mod (inv@215@01 r) step@180@01) N@179@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@226@01 r))
                      (implies
                        (<= 0 (inv@226@01 r))
                        (and
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@226@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@226@01 r) step@180@01))
                                (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                    $k@225@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 2)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@226@01 r))
                      (implies
                        (<= 0 (inv@226@01 r))
                        (and
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@226@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@226@01 r) step@180@01))
                                (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                    $k@225@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@215@01 r))
            :qid |qp.srp25|))
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@215@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@215@01 r))
                        (< (mod (inv@215@01 r) step@180@01) N@179@01)))
                    (/ (to_real 1) (to_real 2))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@215@01 r))
                    (< (mod (inv@215@01 r) step@180@01) N@179@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@226@01 r))
                      (implies
                        (<= 0 (inv@226@01 r))
                        (and
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@226@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@226@01 r) step@180@01))
                                (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                    $k@225@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 2)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@226@01 r))
                      (implies
                        (<= 0 (inv@226@01 r))
                        (and
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@226@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@226@01 r) step@180@01))
                                (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                    $k@225@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@226@01 r))
            :qid |qp.srp25|)))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (<= 0 (inv@226@01 r))
                (implies
                  (<= 0 (inv@226@01 r))
                  (and
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
              (< $Perm.No $k@225@01))
            (= ($Seq.index matrix@181@01 (inv@226@01 r)) r))
          :pattern ((inv@226@01 r))
          :qid |Ref__Integer_value-fctOfInv|))
        (forall ((k@221@01 Int)) (!
          (implies
            (and
              (and
                (<= 0 k@221@01)
                (implies
                  (<= 0 k@221@01)
                  (and
                    (< k@221@01 (* M@178@01 step@180@01))
                    (implies
                      (< k@221@01 (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod k@221@01 step@180@01))
                        (implies
                          (<= 0 (mod k@221@01 step@180@01))
                          (< (mod k@221@01 step@180@01) N@179@01)))))))
              (< $Perm.No $k@225@01))
            (= (inv@226@01 ($Seq.index matrix@181@01 k@221@01)) k@221@01))
          :pattern (($Seq.index matrix@181@01 k@221@01))
          :qid |Ref__Integer_value-invOfFct|))
        (forall ((k@221@01 Int)) (!
          ($Perm.isReadVar $k@225@01 $Perm.Write)
          :pattern (($Seq.index matrix@181@01 k@221@01))
          :qid |Ref__Integer_value-aux|))
        (<= 0 (* M@178@01 step@180@01))
        (> step@180@01 0)
        (<= 0 N@179@01))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (< (mod (inv@215@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
          :qid |qp.fvfValDef24|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (< (mod (inv@215@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
          :qid |qp.fvfValDef24|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
          :qid |qp.fvfValDef23|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
          :qid |qp.fvfValDef23|)))
      ($Seq.contains ($Seq.range 0 P@182@01) k@219@01)))
  :pattern (($Seq.contains ($Seq.range 0 P@182@01) k@219@01))
  :qid |prog.l141-aux|)))
(assert (forall ((k@219@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@219@01)
    (and
      (and
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@225@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@215@01 r))
                    (< (mod (inv@215@01 r) step@180@01) N@179@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r))
            :qid |qp.fvfValDef27|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@225@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@215@01 r))
                    (< (mod (inv@215@01 r) step@180@01) N@179@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
            :qid |qp.fvfValDef27|)))
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@225@01))
                ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r))
            :qid |qp.fvfValDef26|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@226@01 r))
                    (implies
                      (<= 0 (inv@226@01 r))
                      (and
                        (< (inv@226@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@226@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@225@01))
                ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@229@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
            :qid |qp.fvfValDef26|)))
        (forall ((r $Ref)) (!
          (iff
            (Set_in r ($FVF.domain_Ref__Integer_value (as sm@229@01  $FVF<Int>)))
            (and
              (and
                (<= 0 (inv@226@01 r))
                (implies
                  (<= 0 (inv@226@01 r))
                  (and
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
              (< $Perm.No $k@225@01)))
          :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@229@01  $FVF<Int>))))
          :qid |qp.fvfDomDef28|))
        (and
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@215@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@215@01 r))
                        (< (mod (inv@215@01 r) step@180@01) N@179@01)))
                    (/ (to_real 1) (to_real 2))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@215@01 r))
                    (< (mod (inv@215@01 r) step@180@01) N@179@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@226@01 r))
                      (implies
                        (<= 0 (inv@226@01 r))
                        (and
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@226@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@226@01 r) step@180@01))
                                (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                    $k@225@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 2)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@226@01 r))
                      (implies
                        (<= 0 (inv@226@01 r))
                        (and
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@226@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@226@01 r) step@180@01))
                                (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                    $k@225@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@215@01 r))
            :qid |qp.srp25|))
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@215@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@215@01 r))
                        (< (mod (inv@215@01 r) step@180@01) N@179@01)))
                    (/ (to_real 1) (to_real 2))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@215@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@215@01 r))
                    (< (mod (inv@215@01 r) step@180@01) N@179@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@226@01 r))
                      (implies
                        (<= 0 (inv@226@01 r))
                        (and
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@226@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@226@01 r) step@180@01))
                                (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                    $k@225@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 2)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@226@01 r))
                      (implies
                        (<= 0 (inv@226@01 r))
                        (and
                          (< (inv@226@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@226@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@226@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@226@01 r) step@180@01))
                                (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
                    $k@225@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@226@01 r))
            :qid |qp.srp25|)))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (<= 0 (inv@226@01 r))
                (implies
                  (<= 0 (inv@226@01 r))
                  (and
                    (< (inv@226@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@226@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@226@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@226@01 r) step@180@01))
                          (< (mod (inv@226@01 r) step@180@01) N@179@01)))))))
              (< $Perm.No $k@225@01))
            (= ($Seq.index matrix@181@01 (inv@226@01 r)) r))
          :pattern ((inv@226@01 r))
          :qid |Ref__Integer_value-fctOfInv|))
        (forall ((k@221@01 Int)) (!
          (implies
            (and
              (and
                (<= 0 k@221@01)
                (implies
                  (<= 0 k@221@01)
                  (and
                    (< k@221@01 (* M@178@01 step@180@01))
                    (implies
                      (< k@221@01 (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod k@221@01 step@180@01))
                        (implies
                          (<= 0 (mod k@221@01 step@180@01))
                          (< (mod k@221@01 step@180@01) N@179@01)))))))
              (< $Perm.No $k@225@01))
            (= (inv@226@01 ($Seq.index matrix@181@01 k@221@01)) k@221@01))
          :pattern (($Seq.index matrix@181@01 k@221@01))
          :qid |Ref__Integer_value-invOfFct|))
        (forall ((k@221@01 Int)) (!
          ($Perm.isReadVar $k@225@01 $Perm.Write)
          :pattern (($Seq.index matrix@181@01 k@221@01))
          :qid |Ref__Integer_value-aux|))
        (<= 0 (* M@178@01 step@180@01))
        (> step@180@01 0)
        (<= 0 N@179@01))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (< (mod (inv@215@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
          :qid |qp.fvfValDef24|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (< (mod (inv@215@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
          :qid |qp.fvfValDef24|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
          :qid |qp.fvfValDef23|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
          :qid |qp.fvfValDef23|)))
      ($Seq.contains ($Seq.range 0 P@182@01) k@219@01)))
  :pattern ()
  :qid |prog.l141-aux|)))
(assert (and
  (forall ((k@219@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) k@219@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) ($Seq.index
          hist@183@01
          k@219@01))
        (count_square ($Snap.combine
          $Snap.unit
          ($Snap.combine
            $Snap.unit
            ($Snap.combine
              $Snap.unit
              ($Snap.combine
                $Snap.unit
                ($Snap.combine
                  $Snap.unit
                  ($Snap.combine
                    $Snap.unit
                    ($Snap.combine
                      $Snap.unit
                      ($Snap.combine
                        $Snap.unit
                        ($SortWrappers.$FVF<Int>To$Snap (as sm@229@01  $FVF<Int>)))))))))) 0 0 N@179@01 step@180@01 0 (*
          M@178@01
          step@180@01) matrix@181@01 k@219@01)))
    :pattern (($Seq.contains ($Seq.range 0 P@182@01) k@219@01))
    :qid |prog.l141|))
  (forall ((k@219@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) k@219@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) ($Seq.index
          hist@183@01
          k@219@01))
        (count_square ($Snap.combine
          $Snap.unit
          ($Snap.combine
            $Snap.unit
            ($Snap.combine
              $Snap.unit
              ($Snap.combine
                $Snap.unit
                ($Snap.combine
                  $Snap.unit
                  ($Snap.combine
                    $Snap.unit
                    ($Snap.combine
                      $Snap.unit
                      ($Snap.combine
                        $Snap.unit
                        ($SortWrappers.$FVF<Int>To$Snap (as sm@229@01  $FVF<Int>)))))))))) 0 0 N@179@01 step@180@01 0 (*
          M@178@01
          step@180@01) matrix@181@01 k@219@01)))
    :pattern ()
    :qid |prog.l141|))))
; [eval] N <= step
; [eval] (forall k_fresh_rw_0: Int :: { matrix[k_fresh_rw_0] } (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> matrix[k_fresh_rw_0].Ref__Integer_value == old(matrix[k_fresh_rw_0].Ref__Integer_value))
(declare-const k_fresh_rw_0@230@01 Int)
(push) ; 3
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> matrix[k_fresh_rw_0].Ref__Integer_value == old(matrix[k_fresh_rw_0].Ref__Integer_value)
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N
; [eval] (k_fresh_rw_0 in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@231@01 ==> k_fresh_rw_0 % step < N
(push) ; 4
; [then-branch: 24 | k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01] | live]
; [else-branch: 24 | !k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01] | live]
(push) ; 5
; [then-branch: 24 | k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@230@01))
; [eval] k_fresh_rw_0 % step < N
; [eval] k_fresh_rw_0 % step
(push) ; 6
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 142722) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(pop) ; 5
(push) ; 5
; [else-branch: 24 | !k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@230@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(push) ; 4
; [then-branch: 25 | k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@230@01 % step@180@01 < N@179@01 | live]
; [else-branch: 25 | !k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@230@01 % step@180@01 < N@179@01 | live]
(push) ; 5
; [then-branch: 25 | k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@230@01 % step@180@01 < N@179@01]
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@230@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@230@01)
    (< (mod k_fresh_rw_0@230@01 step@180@01) N@179@01))))
; [eval] matrix[k_fresh_rw_0].Ref__Integer_value == old(matrix[k_fresh_rw_0].Ref__Integer_value)
; [eval] matrix[k_fresh_rw_0]
(push) ; 6
(assert (not (>= k_fresh_rw_0@230@01 0)))
 (set-option :rlimit 64554) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k_fresh_rw_0@230@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 34015) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@182@01)
        (inv@218@01 ($Seq.index matrix@181@01 k_fresh_rw_0@230@01)))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          (inv@215@01 ($Seq.index matrix@181@01 k_fresh_rw_0@230@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            (inv@215@01 ($Seq.index matrix@181@01 k_fresh_rw_0@230@01)))
          (<
            (mod
              (inv@215@01 ($Seq.index matrix@181@01 k_fresh_rw_0@230@01))
              step@180@01)
            N@179@01)))
      (/ (to_real 1) (to_real 2))
      $Perm.No)))))
 (set-option :rlimit 6612) (check-sat) 
; unsat
(pop) ; 6
; 0.04s
; 
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
    :qid |qp.fvfValDef23|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
    :qid |qp.fvfValDef23|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
          (< (mod (inv@215@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
    :qid |qp.fvfValDef24|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@215@01 r))
          (< (mod (inv@215@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
    :qid |qp.fvfValDef24|))))
; [eval] old(matrix[k_fresh_rw_0].Ref__Integer_value)
; [eval] matrix[k_fresh_rw_0]
(push) ; 6
(assert (not (>= k_fresh_rw_0@230@01 0)))
 (set-option :rlimit 9893) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k_fresh_rw_0@230@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 22376) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@182@01)
        (inv@204@01 ($Seq.index matrix@181@01 k_fresh_rw_0@230@01)))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@230@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@230@01)))
          (<
            (mod
              (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@230@01))
              step@180@01)
            N@179@01)))
      (/ (to_real 1) (to_real 2))
      $Perm.No)))))
 (set-option :rlimit 81414) (check-sat) 
; unsat
(pop) ; 6
; 0.04s
; 
(declare-const sm@232@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@204@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@202@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r))
    :qid |qp.fvfValDef29|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@204@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@202@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@202@01 r))
    :qid |qp.fvfValDef29|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r))
    :qid |qp.fvfValDef30|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef30|))))
(pop) ; 5
(push) ; 5
; [else-branch: 25 | !k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@230@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@230@01 % step@180@01 < N@179@01]
(assert (not
  (and
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@230@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@230@01)
      (< (mod k_fresh_rw_0@230@01 step@180@01) N@179@01)))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (implies
  (and
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@230@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@230@01)
      (< (mod k_fresh_rw_0@230@01 step@180@01) N@179@01)))
  (and
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r))
        :qid |qp.fvfValDef30|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
        :qid |qp.fvfValDef30|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@204@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@202@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r))
        :qid |qp.fvfValDef29|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@204@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@202@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@202@01 r))
        :qid |qp.fvfValDef29|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (< (mod (inv@215@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
        :qid |qp.fvfValDef24|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@215@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (< (mod (inv@215@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
        :qid |qp.fvfValDef24|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
        :qid |qp.fvfValDef23|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
        :qid |qp.fvfValDef23|)))
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@230@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@230@01)
        (< (mod k_fresh_rw_0@230@01 step@180@01) N@179@01))))))
; Joined path conditions
(pop) ; 3
; Nested auxiliary terms
(assert (forall ((k_fresh_rw_0@230@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@230@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@230@01)
        (< (mod k_fresh_rw_0@230@01 step@180@01) N@179@01)))
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r))
          :qid |qp.fvfValDef30|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef30|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@204@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@202@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r))
          :qid |qp.fvfValDef29|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@204@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@202@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@202@01 r))
          :qid |qp.fvfValDef29|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (< (mod (inv@215@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
          :qid |qp.fvfValDef24|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@215@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@215@01 r))
                (< (mod (inv@215@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@211@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@211@01 r))
          :qid |qp.fvfValDef24|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r))
          :qid |qp.fvfValDef23|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@218@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@216@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@216@01 r))
          :qid |qp.fvfValDef23|)))
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@230@01)
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            k_fresh_rw_0@230@01)
          (< (mod k_fresh_rw_0@230@01 step@180@01) N@179@01)))))
  :pattern (($Seq.index matrix@181@01 k_fresh_rw_0@230@01))
  :qid |prog.l142-aux|)))
(assert (forall ((k_fresh_rw_0@230@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@230@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@230@01)
        (< (mod k_fresh_rw_0@230@01 step@180@01) N@179@01)))
    (=
      ($FVF.lookup_Ref__Integer_value (as sm@220@01  $FVF<Int>) ($Seq.index
        matrix@181@01
        k_fresh_rw_0@230@01))
      ($FVF.lookup_Ref__Integer_value (as sm@232@01  $FVF<Int>) ($Seq.index
        matrix@181@01
        k_fresh_rw_0@230@01))))
  :pattern (($Seq.index matrix@181@01 k_fresh_rw_0@230@01))
  :qid |prog.l142|)))
(pop) ; 2
(push) ; 2
; [exec]
; Ref__loop_main_93(diz, P, hist)
; [eval] diz != null
; [eval] P <= |hist|
; [eval] |hist|
(declare-const k@233@01 Int)
(push) ; 3
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@182@01) k@233@01))
; [eval] hist[k]
(push) ; 4
(assert (not (>= k@233@01 0)))
 (set-option :rlimit 51129) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< k@233@01 ($Seq.length hist@183@01))))
 (set-option :rlimit 76701) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@234@01 ($Ref) Int)
; Nested auxiliary terms
(push) ; 3
(assert (not (forall ((k@233@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@233@01)
    (or (= $Perm.Write $Perm.No) true))
  
  ))))
 (set-option :rlimit 1330688) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Check receiver injectivity
(push) ; 3
(assert (not (forall ((k1@233@01 Int) (k2@233@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 P@182@01) k1@233@01)
      ($Seq.contains ($Seq.range 0 P@182@01) k2@233@01)
      (= ($Seq.index hist@183@01 k1@233@01) ($Seq.index hist@183@01 k2@233@01)))
    (= k1@233@01 k2@233@01))
  
  :qid |Ref__Integer_value-rcvrInj|))))
 (set-option :rlimit 384599) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Definitional axioms for inverse functions
(assert (forall ((k@233@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@233@01)
    (= (inv@234@01 ($Seq.index hist@183@01 k@233@01)) k@233@01))
  :pattern (($Seq.index hist@183@01 k@233@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@234@01 r))
    (= ($Seq.index hist@183@01 (inv@234@01 r)) r))
  :pattern ((inv@234@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@235@01 ((r $Ref)) $Perm
  (ite
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@234@01 r))
    ($Perm.min
      (ite
        ($Seq.contains ($Seq.range 0 P@182@01) (inv@204@01 r))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
(define-fun pTaken@236@01 ((r $Ref)) $Perm
  (ite
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@234@01 r))
    ($Perm.min
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (< (mod (inv@196@01 r) step@180@01) N@179@01)))
        (/ (to_real 1) (to_real 2))
        $Perm.No)
      (- $Perm.Write (pTaken@235@01 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
;(set-option :timeout 10)
 (set-option :rlimit 7966) (check-sat) 
; unknown
; Chunk depleted?
;(set-option :timeout 500)
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (ite
        ($Seq.contains ($Seq.range 0 P@182@01) (inv@204@01 r))
        $Perm.Write
        $Perm.No)
      (pTaken@235@01 r))
    $Perm.No)
  
  ))))
 (set-option :rlimit 62965) (check-sat) 
; unsat
(pop) ; 3
; 0.01s
; 
; Intermediate check if already taken enough permissions
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@234@01 r))
    (= (- $Perm.Write (pTaken@235@01 r)) $Perm.No))
  
  ))))
 (set-option :rlimit 23130) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@237@01 $FVF<Int>)
; Definitional axioms for SM values
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@204@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@237@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@202@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@237@01  $FVF<Int>) r))
    :qid |qp.fvfValDef31|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@204@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@237@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@202@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@202@01 r))
    :qid |qp.fvfValDef31|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@237@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@237@01  $FVF<Int>) r))
    :qid |qp.fvfValDef32|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@237@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef32|))))
(declare-const $t@238@01 $Snap)
(declare-const $t@239@01 $FVF<Int>)
(assert (=
  $t@238@01
  ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@239@01) $Snap.unit)))
(declare-const k@240@01 Int)
(push) ; 3
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@182@01) k@240@01))
; [eval] hist[k]
;(set-option :timeout 0)
(push) ; 4
(assert (not (>= k@240@01 0)))
 (set-option :rlimit 12138) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< k@240@01 ($Seq.length hist@183@01))))
 (set-option :rlimit 28800) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@241@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((k@240@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@240@01)
    (= (inv@241@01 ($Seq.index hist@183@01 k@240@01)) k@240@01))
  :pattern (($Seq.index hist@183@01 k@240@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
    (= ($Seq.index hist@183@01 (inv@241@01 r)) r))
  :pattern ((inv@241@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((k@240@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@240@01)
    (not (= ($Seq.index hist@183@01 k@240@01) $Ref.null)))
  :pattern (($Seq.index hist@183@01 k@240@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
; [eval] (forall k: Int :: { (k in [0..P)) } { hist[k] } (k in [0..P)) ==> hist[k].Ref__Integer_value == 0)
(declare-const k@242@01 Int)
(push) ; 3
; [eval] (k in [0..P)) ==> hist[k].Ref__Integer_value == 0
; [eval] (k in [0..P))
; [eval] [0..P)
(push) ; 4
; [then-branch: 26 | k@242@01 in [0..P@182@01] | live]
; [else-branch: 26 | !k@242@01 in [0..P@182@01] | live]
(push) ; 5
; [then-branch: 26 | k@242@01 in [0..P@182@01]]
(assert ($Seq.contains ($Seq.range 0 P@182@01) k@242@01))
; [eval] hist[k].Ref__Integer_value == 0
; [eval] hist[k]
(push) ; 6
(assert (not (>= k@242@01 0)))
 (set-option :rlimit 57111) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k@242@01 ($Seq.length hist@183@01))))
 (set-option :rlimit 7076) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@182@01)
        (inv@241@01 ($Seq.index hist@183@01 k@242@01)))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          (inv@196@01 ($Seq.index hist@183@01 k@242@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            (inv@196@01 ($Seq.index hist@183@01 k@242@01)))
          (<
            (mod (inv@196@01 ($Seq.index hist@183@01 k@242@01)) step@180@01)
            N@179@01)))
      (/ (to_real 1) (to_real 2))
      $Perm.No)))))
 (set-option :rlimit 11321) (check-sat) 
; unsat
(pop) ; 6
; 0.01s
; 
(declare-const sm@243@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
    :qid |qp.fvfValDef33|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
    :qid |qp.fvfValDef33|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
    :qid |qp.fvfValDef34|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef34|))))
(pop) ; 5
(push) ; 5
; [else-branch: 26 | !k@242@01 in [0..P@182@01]]
(assert (not ($Seq.contains ($Seq.range 0 P@182@01) k@242@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (implies
  ($Seq.contains ($Seq.range 0 P@182@01) k@242@01)
  (and
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
        :qid |qp.fvfValDef34|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
        :qid |qp.fvfValDef34|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
        :qid |qp.fvfValDef33|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
        :qid |qp.fvfValDef33|)))
    ($Seq.contains ($Seq.range 0 P@182@01) k@242@01))))
; Joined path conditions
(pop) ; 3
; Nested auxiliary terms
(assert (forall ((k@242@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@242@01)
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef34|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef34|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef33|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
          :qid |qp.fvfValDef33|)))
      ($Seq.contains ($Seq.range 0 P@182@01) k@242@01)))
  :pattern (($Seq.contains ($Seq.range 0 P@182@01) k@242@01))
  :qid |prog.l56-aux|)))
(assert (forall ((k@242@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@242@01)
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef34|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef34|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef33|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
          :qid |qp.fvfValDef33|)))
      ($Seq.contains ($Seq.range 0 P@182@01) k@242@01)))
  :pattern (($Seq.index hist@183@01 k@242@01))
  :qid |prog.l56-aux|)))
(assert (and
  (forall ((k@242@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) k@242@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) ($Seq.index
          hist@183@01
          k@242@01))
        0))
    :pattern (($Seq.contains ($Seq.range 0 P@182@01) k@242@01))
    :qid |prog.l56|))
  (forall ((k@242@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) k@242@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) ($Seq.index
          hist@183@01
          k@242@01))
        0))
    :pattern (($Seq.index hist@183@01 k@242@01))
    :qid |prog.l56|))))
; State saturation: after contract
;(set-option :timeout 50)
 (set-option :rlimit 3551) (check-sat) 
; unknown
; [exec]
; Ref__loop_main_113(diz, N, M, step, hist, matrix, P)
; [eval] diz != null
; [eval] M > 0
; [eval] N > 0
; [eval] step >= N
; [eval] P > 0
; [eval] P <= |hist|
; [eval] |hist|
(declare-const k@244@01 Int)
(push) ; 3
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@182@01) k@244@01))
; [eval] hist[k]
;(set-option :timeout 0)
(push) ; 4
(assert (not (>= k@244@01 0)))
 (set-option :rlimit 15488) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< k@244@01 ($Seq.length hist@183@01))))
 (set-option :rlimit 33096) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@245@01 ($Ref) Int)
; Nested auxiliary terms
(push) ; 3
(assert (not (forall ((k@244@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@244@01)
    (or (= $Perm.Write $Perm.No) true))
  
  ))))
 (set-option :rlimit 9219) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Check receiver injectivity
(push) ; 3
(assert (not (forall ((k1@244@01 Int) (k2@244@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 P@182@01) k1@244@01)
      ($Seq.contains ($Seq.range 0 P@182@01) k2@244@01)
      (= ($Seq.index hist@183@01 k1@244@01) ($Seq.index hist@183@01 k2@244@01)))
    (= k1@244@01 k2@244@01))
  
  :qid |Ref__Integer_value-rcvrInj|))))
 (set-option :rlimit 14937) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Definitional axioms for inverse functions
(assert (forall ((k@244@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@244@01)
    (= (inv@245@01 ($Seq.index hist@183@01 k@244@01)) k@244@01))
  :pattern (($Seq.index hist@183@01 k@244@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@245@01 r))
    (= ($Seq.index hist@183@01 (inv@245@01 r)) r))
  :pattern ((inv@245@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@246@01 ((r $Ref)) $Perm
  (ite
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@245@01 r))
    ($Perm.min
      (ite
        ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
(define-fun pTaken@247@01 ((r $Ref)) $Perm
  (ite
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@245@01 r))
    ($Perm.min
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (< (mod (inv@196@01 r) step@180@01) N@179@01)))
        (/ (to_real 1) (to_real 2))
        $Perm.No)
      (- $Perm.Write (pTaken@246@01 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
;(set-option :timeout 10)
 (set-option :rlimit 216242) (check-sat) 
; unknown
; Chunk depleted?
;(set-option :timeout 500)
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (ite
        ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
        $Perm.Write
        $Perm.No)
      (pTaken@246@01 r))
    $Perm.No)
  
  ))))
 (set-option :rlimit 31960) (check-sat) 
; unsat
(pop) ; 3
; 0.01s
; 
; Intermediate check if already taken enough permissions
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@245@01 r))
    (= (- $Perm.Write (pTaken@246@01 r)) $Perm.No))
  
  ))))
 (set-option :rlimit 242728) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@248@01 $FVF<Int>)
; Definitional axioms for SM values
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@248@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@248@01  $FVF<Int>) r))
    :qid |qp.fvfValDef35|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@248@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
    :qid |qp.fvfValDef35|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@248@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@248@01  $FVF<Int>) r))
    :qid |qp.fvfValDef36|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@248@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef36|))))
; [eval] N <= step
; [eval] M * step <= |matrix|
; [eval] M * step
; [eval] |matrix|
(declare-const j@249@01 Int)
(push) ; 3
; [eval] (j in [0..M * step)) && j % step < N
; [eval] (j in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@250@01 ==> j % step < N
(push) ; 4
; [then-branch: 27 | j@249@01 in [0..M@178@01 * step@180@01] | live]
; [else-branch: 27 | !j@249@01 in [0..M@178@01 * step@180@01] | live]
(push) ; 5
; [then-branch: 27 | j@249@01 in [0..M@178@01 * step@180@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@249@01))
; [eval] j % step < N
; [eval] j % step
;(set-option :timeout 0)
(push) ; 6
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 20843) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(pop) ; 5
(push) ; 5
; [else-branch: 27 | !j@249@01 in [0..M@178@01 * step@180@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@249@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@249@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@249@01)
    (< (mod j@249@01 step@180@01) N@179@01))))
(push) ; 4
(assert (not (not (= 4 0))))
 (set-option :rlimit 219876) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
; [eval] matrix[j]
(push) ; 4
(assert (not (>= j@249@01 0)))
 (set-option :rlimit 51953) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< j@249@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 9392) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@251@01 ($Ref) Int)
; Nested auxiliary terms
(push) ; 3
(assert (not (forall ((j@249@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@249@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@249@01)
        (< (mod j@249@01 step@180@01) N@179@01)))
    (or (= (/ (to_real 1) (to_real 4)) $Perm.No) true))
  
  ))))
 (set-option :rlimit 103936) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Check receiver injectivity
(push) ; 3
(assert (not (forall ((j1@249@01 Int) (j2@249@01 Int)) (!
  (implies
    (and
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@249@01)
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@249@01)
          (< (mod j1@249@01 step@180@01) N@179@01)))
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j2@249@01)
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j2@249@01)
          (< (mod j2@249@01 step@180@01) N@179@01)))
      (=
        ($Seq.index matrix@181@01 j1@249@01)
        ($Seq.index matrix@181@01 j2@249@01)))
    (= j1@249@01 j2@249@01))
  
  :qid |Ref__Integer_value-rcvrInj|))))
 (set-option :rlimit 2019) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Definitional axioms for inverse functions
(assert (forall ((j@249@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@249@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@249@01)
        (< (mod j@249@01 step@180@01) N@179@01)))
    (= (inv@251@01 ($Seq.index matrix@181@01 j@249@01)) j@249@01))
  :pattern (($Seq.index matrix@181@01 j@249@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@251@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@251@01 r))
        (< (mod (inv@251@01 r) step@180@01) N@179@01)))
    (= ($Seq.index matrix@181@01 (inv@251@01 r)) r))
  :pattern ((inv@251@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@252@01 ((r $Ref)) $Perm
  (ite
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@251@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@251@01 r))
        (< (mod (inv@251@01 r) step@180@01) N@179@01)))
    ($Perm.min
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (< (mod (inv@196@01 r) step@180@01) N@179@01)))
        (/ (to_real 1) (to_real 2))
        $Perm.No)
      (/ (to_real 1) (to_real 4)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
;(set-option :timeout 10)
 (set-option :rlimit 92072) (check-sat) 
; unknown
; Chunk depleted?
;(set-option :timeout 500)
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (< (mod (inv@196@01 r) step@180@01) N@179@01)))
        (/ (to_real 1) (to_real 2))
        $Perm.No)
      (pTaken@252@01 r))
    $Perm.No)
  
  ))))
 (set-option :rlimit 79559) (check-sat) 
; unknown
(pop) ; 3
; 0.05s
; 
; Intermediate check if already taken enough permissions
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@251@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@251@01 r))
        (< (mod (inv@251@01 r) step@180@01) N@179@01)))
    (= (- (/ (to_real 1) (to_real 4)) (pTaken@252@01 r)) $Perm.No))
  
  ))))
 (set-option :rlimit 1988) (check-sat) 
; unsat
(pop) ; 3
; 0.01s
; 
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@253@01 $FVF<Int>)
; Definitional axioms for SM values
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@253@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@253@01  $FVF<Int>) r))
    :qid |qp.fvfValDef37|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@253@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef37|))))
; [eval] N <= step
; [eval] (forall k_fresh_rw_0: Int :: { (matrix[k_fresh_rw_0].Ref__Integer_value in [0..P)) } (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> (matrix[k_fresh_rw_0].Ref__Integer_value in [0..P)))
(declare-const k_fresh_rw_0@254@01 Int)
(push) ; 3
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> (matrix[k_fresh_rw_0].Ref__Integer_value in [0..P))
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N
; [eval] (k_fresh_rw_0 in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@255@01 ==> k_fresh_rw_0 % step < N
(push) ; 4
; [then-branch: 28 | k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01] | live]
; [else-branch: 28 | !k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01] | live]
(push) ; 5
; [then-branch: 28 | k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01))
; [eval] k_fresh_rw_0 % step < N
; [eval] k_fresh_rw_0 % step
;(set-option :timeout 0)
(push) ; 6
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 15646) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(pop) ; 5
(push) ; 5
; [else-branch: 28 | !k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(push) ; 4
; [then-branch: 29 | k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@254@01 % step@180@01 < N@179@01 | live]
; [else-branch: 29 | !k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@254@01 % step@180@01 < N@179@01 | live]
(push) ; 5
; [then-branch: 29 | k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@254@01 % step@180@01 < N@179@01]
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01)
    (< (mod k_fresh_rw_0@254@01 step@180@01) N@179@01))))
; [eval] (matrix[k_fresh_rw_0].Ref__Integer_value in [0..P))
; [eval] [0..P)
; [eval] matrix[k_fresh_rw_0]
(push) ; 6
(assert (not (>= k_fresh_rw_0@254@01 0)))
 (set-option :rlimit 2735) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k_fresh_rw_0@254@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 27227) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@182@01)
        (inv@241@01 ($Seq.index matrix@181@01 k_fresh_rw_0@254@01)))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@254@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@254@01)))
          (<
            (mod
              (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@254@01))
              step@180@01)
            N@179@01)))
      (/ (to_real 1) (to_real 2))
      $Perm.No)))))
 (set-option :rlimit 31528) (check-sat) 
; unsat
(pop) ; 6
; 0.01s
; 
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
    :qid |qp.fvfValDef33|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
    :qid |qp.fvfValDef33|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
    :qid |qp.fvfValDef34|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef34|))))
(pop) ; 5
(push) ; 5
; [else-branch: 29 | !k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@254@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@254@01 % step@180@01 < N@179@01]
(assert (not
  (and
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01)
      (< (mod k_fresh_rw_0@254@01 step@180@01) N@179@01)))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (implies
  (and
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01)
      (< (mod k_fresh_rw_0@254@01 step@180@01) N@179@01)))
  (and
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
        :qid |qp.fvfValDef34|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
        :qid |qp.fvfValDef34|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
        :qid |qp.fvfValDef33|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
        :qid |qp.fvfValDef33|)))
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@254@01)
        (< (mod k_fresh_rw_0@254@01 step@180@01) N@179@01))))))
; Joined path conditions
(declare-const fvf@256@01 $FVF<Int>)
(pop) ; 3
; Nested auxiliary terms
(assert (forall ((k_fresh_rw_0@254@01 Int) (fvf@256@01 $FVF<Int>)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@254@01)
        (< (mod k_fresh_rw_0@254@01 step@180@01) N@179@01)))
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef34|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef34|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef33|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
          :qid |qp.fvfValDef33|)))
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@254@01)
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            k_fresh_rw_0@254@01)
          (< (mod k_fresh_rw_0@254@01 step@180@01) N@179@01)))))
  :pattern (($Seq.contains
    ($Seq.range 0 P@182@01)
    ($FVF.lookup_Ref__Integer_value fvf@256@01 ($Seq.index
      matrix@181@01
      k_fresh_rw_0@254@01))))
  :qid |prog.l83-aux|)))
(push) ; 3
(assert (not (forall ((k_fresh_rw_0@254@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@254@01)
        (< (mod k_fresh_rw_0@254@01 step@180@01) N@179@01)))
    ($Seq.contains
      ($Seq.range 0 P@182@01)
      ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) ($Seq.index
        matrix@181@01
        k_fresh_rw_0@254@01))))
  :pattern (($Seq.contains
    ($Seq.range 0 P@182@01)
    ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) ($Seq.index
      matrix@181@01
      k_fresh_rw_0@254@01))))
  :qid |prog.l83|))))
 (set-option :rlimit 337499) (check-sat) 
; unsat
(pop) ; 3
; 0.01s
; 
(assert (forall ((k_fresh_rw_0@254@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@254@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@254@01)
        (< (mod k_fresh_rw_0@254@01 step@180@01) N@179@01)))
    ($Seq.contains
      ($Seq.range 0 P@182@01)
      ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) ($Seq.index
        matrix@181@01
        k_fresh_rw_0@254@01))))
  :pattern (($Seq.contains
    ($Seq.range 0 P@182@01)
    ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) ($Seq.index
      matrix@181@01
      k_fresh_rw_0@254@01))))
  :qid |prog.l83|)))
(declare-const $t@257@01 $Snap)
(declare-const $t@258@01 $Snap)
(assert (= $t@257@01 ($Snap.combine $Snap.unit $t@258@01)))
; [eval] M > 0
(declare-const $t@259@01 $Snap)
(assert (= $t@258@01 ($Snap.combine $Snap.unit $t@259@01)))
; [eval] N > 0
(declare-const $t@260@01 $Snap)
(assert (= $t@259@01 ($Snap.combine $Snap.unit $t@260@01)))
; [eval] step >= N
(declare-const $t@261@01 $Snap)
(assert (= $t@260@01 ($Snap.combine $Snap.unit $t@261@01)))
; [eval] P > 0
(declare-const $t@262@01 $Snap)
(assert (= $t@261@01 ($Snap.combine $Snap.unit $t@262@01)))
; [eval] N <= step
(declare-const $t@263@01 $FVF<Int>)
(declare-const $t@264@01 $Snap)
(assert (=
  $t@262@01
  ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@263@01) $t@264@01)))
(declare-const j@265@01 Int)
(push) ; 3
; [eval] (j in [0..M * step)) && j % step < N
; [eval] (j in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@266@01 ==> j % step < N
(push) ; 4
; [then-branch: 30 | j@265@01 in [0..M@178@01 * step@180@01] | live]
; [else-branch: 30 | !j@265@01 in [0..M@178@01 * step@180@01] | live]
(push) ; 5
; [then-branch: 30 | j@265@01 in [0..M@178@01 * step@180@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@265@01))
; [eval] j % step < N
; [eval] j % step
(push) ; 6
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 6352) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(pop) ; 5
(push) ; 5
; [else-branch: 30 | !j@265@01 in [0..M@178@01 * step@180@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@265@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@265@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@265@01)
    (< (mod j@265@01 step@180@01) N@179@01))))
; [eval] matrix[j]
(push) ; 4
(assert (not (>= j@265@01 0)))
 (set-option :rlimit 8956) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< j@265@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 161511) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (not (= 4 0))))
 (set-option :rlimit 61575) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@267@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((j@265@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@265@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@265@01)
        (< (mod j@265@01 step@180@01) N@179@01)))
    (= (inv@267@01 ($Seq.index matrix@181@01 j@265@01)) j@265@01))
  :pattern (($Seq.index matrix@181@01 j@265@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
        (< (mod (inv@267@01 r) step@180@01) N@179@01)))
    (= ($Seq.index matrix@181@01 (inv@267@01 r)) r))
  :pattern ((inv@267@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((j@265@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@265@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j@265@01)
        (< (mod j@265@01 step@180@01) N@179@01)))
    (not (= ($Seq.index matrix@181@01 j@265@01) $Ref.null)))
  :pattern (($Seq.index matrix@181@01 j@265@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
(declare-const $t@268@01 $FVF<Int>)
(assert (=
  $t@264@01
  ($Snap.combine ($SortWrappers.$FVF<Int>To$Snap $t@268@01) $Snap.unit)))
(declare-const k@269@01 Int)
(push) ; 3
; [eval] (k in [0..P))
; [eval] [0..P)
(assert ($Seq.contains ($Seq.range 0 P@182@01) k@269@01))
; [eval] hist[k]
(push) ; 4
(assert (not (>= k@269@01 0)))
 (set-option :rlimit 5795) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< k@269@01 ($Seq.length hist@183@01))))
 (set-option :rlimit 13732) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@270@01 ($Ref) Int)
; Nested auxiliary terms
; Definitional axioms for inverse functions
(assert (forall ((k@269@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@269@01)
    (= (inv@270@01 ($Seq.index hist@183@01 k@269@01)) k@269@01))
  :pattern (($Seq.index hist@183@01 k@269@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
    (= ($Seq.index hist@183@01 (inv@270@01 r)) r))
  :pattern ((inv@270@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Permissions are non-negative
; Field permissions are at most one
; Permission implies non-null receiver
(assert (forall ((k@269@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@269@01)
    (not (= ($Seq.index hist@183@01 k@269@01) $Ref.null)))
  :pattern (($Seq.index hist@183@01 k@269@01))
  :qid |Ref__Integer_value-permImpliesNonNull|)))
; [eval] (forall k: Int :: { (k in [0..P)) } { hist[k] } (k in [0..P)) ==> hist[k].Ref__Integer_value == old(hist[k].Ref__Integer_value) + count_square(0, 0, N, step, 0, M * step, matrix, k))
(declare-const k@271@01 Int)
(push) ; 3
; [eval] (k in [0..P)) ==> hist[k].Ref__Integer_value == old(hist[k].Ref__Integer_value) + count_square(0, 0, N, step, 0, M * step, matrix, k)
; [eval] (k in [0..P))
; [eval] [0..P)
(push) ; 4
; [then-branch: 31 | k@271@01 in [0..P@182@01] | live]
; [else-branch: 31 | !k@271@01 in [0..P@182@01] | live]
(push) ; 5
; [then-branch: 31 | k@271@01 in [0..P@182@01]]
(assert ($Seq.contains ($Seq.range 0 P@182@01) k@271@01))
; [eval] hist[k].Ref__Integer_value == old(hist[k].Ref__Integer_value) + count_square(0, 0, N, step, 0, M * step, matrix, k)
; [eval] hist[k]
(push) ; 6
(assert (not (>= k@271@01 0)))
 (set-option :rlimit 93027) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k@271@01 ($Seq.length hist@183@01))))
 (set-option :rlimit 6559) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        ($Seq.contains
          ($Seq.range 0 P@182@01)
          (inv@270@01 ($Seq.index hist@183@01 k@271@01)))
        $Perm.Write
        $Perm.No)
      (ite
        (and
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            (inv@267@01 ($Seq.index hist@183@01 k@271@01)))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 ($Seq.index hist@183@01 k@271@01)))
            (<
              (mod (inv@267@01 ($Seq.index hist@183@01 k@271@01)) step@180@01)
              N@179@01)))
        (/ (to_real 1) (to_real 4))
        $Perm.No))
    (-
      (ite
        (and
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            (inv@196@01 ($Seq.index hist@183@01 k@271@01)))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 ($Seq.index hist@183@01 k@271@01)))
            (<
              (mod (inv@196@01 ($Seq.index hist@183@01 k@271@01)) step@180@01)
              N@179@01)))
        (/ (to_real 1) (to_real 2))
        $Perm.No)
      (pTaken@252@01 ($Seq.index hist@183@01 k@271@01)))))))
 (set-option :rlimit 4447) (check-sat) 
; unsat
(pop) ; 6
; 0.04s
; 
(declare-const sm@272@01 $FVF<Int>)
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
    :qid |qp.fvfValDef38|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
    :qid |qp.fvfValDef38|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
          (< (mod (inv@267@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
    :qid |qp.fvfValDef39|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
          (< (mod (inv@267@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
    :qid |qp.fvfValDef39|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (<
        $Perm.No
        (-
          (ite
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (/ (to_real 1) (to_real 2))
            $Perm.No)
          (pTaken@252@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
    :qid |qp.fvfValDef40|))
  (forall ((r $Ref)) (!
    (implies
      (<
        $Perm.No
        (-
          (ite
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (/ (to_real 1) (to_real 2))
            $Perm.No)
          (pTaken@252@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef40|))))
; [eval] old(hist[k].Ref__Integer_value) + count_square(0, 0, N, step, 0, M * step, matrix, k)
; [eval] old(hist[k].Ref__Integer_value)
; [eval] hist[k]
(push) ; 6
(assert (not (>= k@271@01 0)))
 (set-option :rlimit 891) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k@271@01 ($Seq.length hist@183@01))))
 (set-option :rlimit 6982) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@182@01)
        (inv@241@01 ($Seq.index hist@183@01 k@271@01)))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          (inv@196@01 ($Seq.index hist@183@01 k@271@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            (inv@196@01 ($Seq.index hist@183@01 k@271@01)))
          (<
            (mod (inv@196@01 ($Seq.index hist@183@01 k@271@01)) step@180@01)
            N@179@01)))
      (/ (to_real 1) (to_real 2))
      $Perm.No)))))
 (set-option :rlimit 35556) (check-sat) 
; unsat
(pop) ; 6
; 0.01s
; 
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
    :qid |qp.fvfValDef33|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
    :qid |qp.fvfValDef33|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
    :qid |qp.fvfValDef34|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef34|))))
; [eval] count_square(0, 0, N, step, 0, M * step, matrix, k)
; [eval] M * step
(push) ; 6
; [eval] 0 <= 0
; [eval] 0 <= N
(push) ; 7
(assert (not (<= 0 N@179@01)))
 (set-option :rlimit 2730) (check-sat) 
; unsat
(pop) ; 7
; 0.00s
; 
(assert (<= 0 N@179@01))
; [eval] N <= step
; [eval] step > 0
(push) ; 7
(assert (not (> step@180@01 0)))
 (set-option :rlimit 230904) (check-sat) 
; unsat
(pop) ; 7
; 0.00s
; 
(assert (> step@180@01 0))
; [eval] 0 <= 0
; [eval] 0 <= 0
; [eval] 0 <= M * step
; [eval] M * step
(push) ; 7
(assert (not (<= 0 (* M@178@01 step@180@01))))
 (set-option :rlimit 20243) (check-sat) 
; unsat
(pop) ; 7
; 0.03s
; 
(assert (<= 0 (* M@178@01 step@180@01)))
; [eval] M * step <= |matrix|
; [eval] M * step
; [eval] |matrix|
(declare-const k@273@01 Int)
(push) ; 7
; [eval] 0 <= k && (k < M * step && (0 <= k % step && k % step < N))
; [eval] 0 <= k
; [eval] v@274@01 ==> k < M * step && (0 <= k % step && k % step < N)
(push) ; 8
; [then-branch: 32 | 0 <= k@273@01 | live]
; [else-branch: 32 | !0 <= k@273@01 | live]
(push) ; 9
; [then-branch: 32 | 0 <= k@273@01]
(assert (<= 0 k@273@01))
; [eval] k < M * step && (0 <= k % step && k % step < N)
; [eval] k < M * step
; [eval] M * step
; [eval] v@275@01 ==> 0 <= k % step && k % step < N
(push) ; 10
; [then-branch: 33 | k@273@01 < M@178@01 * step@180@01 | live]
; [else-branch: 33 | !k@273@01 < M@178@01 * step@180@01 | live]
(push) ; 11
; [then-branch: 33 | k@273@01 < M@178@01 * step@180@01]
(assert (< k@273@01 (* M@178@01 step@180@01)))
; [eval] 0 <= k % step && k % step < N
; [eval] 0 <= k % step
; [eval] k % step
(push) ; 12
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 40770) (check-sat) 
; unsat
(pop) ; 12
; 0.00s
; 
; [eval] v@276@01 ==> k % step < N
(push) ; 12
; [then-branch: 34 | 0 <= k@273@01 % step@180@01 | live]
; [else-branch: 34 | !0 <= k@273@01 % step@180@01 | live]
(push) ; 13
; [then-branch: 34 | 0 <= k@273@01 % step@180@01]
(assert (<= 0 (mod k@273@01 step@180@01)))
; [eval] k % step < N
; [eval] k % step
(push) ; 14
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 102255) (check-sat) 
; unsat
(pop) ; 14
; 0.00s
; 
(pop) ; 13
(push) ; 13
; [else-branch: 34 | !0 <= k@273@01 % step@180@01]
(assert (not (<= 0 (mod k@273@01 step@180@01))))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
(pop) ; 11
(push) ; 11
; [else-branch: 33 | !k@273@01 < M@178@01 * step@180@01]
(assert (not (< k@273@01 (* M@178@01 step@180@01))))
(pop) ; 11
(pop) ; 10
; Joined path conditions
; Joined path conditions
(pop) ; 9
(push) ; 9
; [else-branch: 32 | !0 <= k@273@01]
(assert (not (<= 0 k@273@01)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (and
  (<= 0 k@273@01)
  (implies
    (<= 0 k@273@01)
    (and
      (< k@273@01 (* M@178@01 step@180@01))
      (implies
        (< k@273@01 (* M@178@01 step@180@01))
        (and
          (<= 0 (mod k@273@01 step@180@01))
          (implies
            (<= 0 (mod k@273@01 step@180@01))
            (< (mod k@273@01 step@180@01) N@179@01))))))))
(declare-const $k@277@01 $Perm)
(assert ($Perm.isReadVar $k@277@01 $Perm.Write))
; [eval] matrix[k]
(push) ; 8
(assert (not (>= k@273@01 0)))
 (set-option :rlimit 110983) (check-sat) 
; unsat
(pop) ; 8
; 0.00s
; 
(push) ; 8
(assert (not (< k@273@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 20348) (check-sat) 
; unsat
(pop) ; 8
; 0.00s
; 
(pop) ; 7
(declare-fun inv@278@01 ($Ref) Int)
; Nested auxiliary terms
(assert (forall ((k@273@01 Int)) (!
  ($Perm.isReadVar $k@277@01 $Perm.Write)
  :pattern (($Seq.index matrix@181@01 k@273@01))
  :qid |Ref__Integer_value-aux|)))
(push) ; 7
(assert (not (forall ((k@273@01 Int)) (!
  (implies
    (and
      (<= 0 k@273@01)
      (implies
        (<= 0 k@273@01)
        (and
          (< k@273@01 (* M@178@01 step@180@01))
          (implies
            (< k@273@01 (* M@178@01 step@180@01))
            (and
              (<= 0 (mod k@273@01 step@180@01))
              (implies
                (<= 0 (mod k@273@01 step@180@01))
                (< (mod k@273@01 step@180@01) N@179@01)))))))
    (or (= $k@277@01 $Perm.No) (< $Perm.No $k@277@01)))
  
  ))))
 (set-option :rlimit 24364) (check-sat) 
; unsat
(pop) ; 7
; 0.00s
; 
; Check receiver injectivity
(push) ; 7
(assert (not (forall ((k1@273@01 Int) (k2@273@01 Int)) (!
  (implies
    (and
      (and
        (and
          (<= 0 k1@273@01)
          (implies
            (<= 0 k1@273@01)
            (and
              (< k1@273@01 (* M@178@01 step@180@01))
              (implies
                (< k1@273@01 (* M@178@01 step@180@01))
                (and
                  (<= 0 (mod k1@273@01 step@180@01))
                  (implies
                    (<= 0 (mod k1@273@01 step@180@01))
                    (< (mod k1@273@01 step@180@01) N@179@01)))))))
        (< $Perm.No $k@277@01))
      (and
        (and
          (<= 0 k2@273@01)
          (implies
            (<= 0 k2@273@01)
            (and
              (< k2@273@01 (* M@178@01 step@180@01))
              (implies
                (< k2@273@01 (* M@178@01 step@180@01))
                (and
                  (<= 0 (mod k2@273@01 step@180@01))
                  (implies
                    (<= 0 (mod k2@273@01 step@180@01))
                    (< (mod k2@273@01 step@180@01) N@179@01)))))))
        (< $Perm.No $k@277@01))
      (=
        ($Seq.index matrix@181@01 k1@273@01)
        ($Seq.index matrix@181@01 k2@273@01)))
    (= k1@273@01 k2@273@01))
  
  :qid |Ref__Integer_value-rcvrInj|))))
 (set-option :rlimit 12557) (check-sat) 
; unsat
(pop) ; 7
; 0.03s
; 
; Definitional axioms for inverse functions
(assert (forall ((k@273@01 Int)) (!
  (implies
    (and
      (and
        (<= 0 k@273@01)
        (implies
          (<= 0 k@273@01)
          (and
            (< k@273@01 (* M@178@01 step@180@01))
            (implies
              (< k@273@01 (* M@178@01 step@180@01))
              (and
                (<= 0 (mod k@273@01 step@180@01))
                (implies
                  (<= 0 (mod k@273@01 step@180@01))
                  (< (mod k@273@01 step@180@01) N@179@01)))))))
      (< $Perm.No $k@277@01))
    (= (inv@278@01 ($Seq.index matrix@181@01 k@273@01)) k@273@01))
  :pattern (($Seq.index matrix@181@01 k@273@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    (and
      (and
        (<= 0 (inv@278@01 r))
        (implies
          (<= 0 (inv@278@01 r))
          (and
            (< (inv@278@01 r) (* M@178@01 step@180@01))
            (implies
              (< (inv@278@01 r) (* M@178@01 step@180@01))
              (and
                (<= 0 (mod (inv@278@01 r) step@180@01))
                (implies
                  (<= 0 (mod (inv@278@01 r) step@180@01))
                  (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
      (< $Perm.No $k@277@01))
    (= ($Seq.index matrix@181@01 (inv@278@01 r)) r))
  :pattern ((inv@278@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@279@01 ((r $Ref)) $Perm
  (ite
    (and
      (<= 0 (inv@278@01 r))
      (implies
        (<= 0 (inv@278@01 r))
        (and
          (< (inv@278@01 r) (* M@178@01 step@180@01))
          (implies
            (< (inv@278@01 r) (* M@178@01 step@180@01))
            (and
              (<= 0 (mod (inv@278@01 r) step@180@01))
              (implies
                (<= 0 (mod (inv@278@01 r) step@180@01))
                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
    ($Perm.min
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (< (mod (inv@267@01 r) step@180@01) N@179@01)))
        (/ (to_real 1) (to_real 4))
        $Perm.No)
      $k@277@01)
    $Perm.No))
(define-fun pTaken@280@01 ((r $Ref)) $Perm
  (ite
    (and
      (<= 0 (inv@278@01 r))
      (implies
        (<= 0 (inv@278@01 r))
        (and
          (< (inv@278@01 r) (* M@178@01 step@180@01))
          (implies
            (< (inv@278@01 r) (* M@178@01 step@180@01))
            (and
              (<= 0 (mod (inv@278@01 r) step@180@01))
              (implies
                (<= 0 (mod (inv@278@01 r) step@180@01))
                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
    ($Perm.min
      (-
        (ite
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (/ (to_real 1) (to_real 2))
          $Perm.No)
        (pTaken@252@01 r))
      (- $k@277@01 (pTaken@279@01 r)))
    $Perm.No))
(define-fun pTaken@281@01 ((r $Ref)) $Perm
  (ite
    (and
      (<= 0 (inv@278@01 r))
      (implies
        (<= 0 (inv@278@01 r))
        (and
          (< (inv@278@01 r) (* M@178@01 step@180@01))
          (implies
            (< (inv@278@01 r) (* M@178@01 step@180@01))
            (and
              (<= 0 (mod (inv@278@01 r) step@180@01))
              (implies
                (<= 0 (mod (inv@278@01 r) step@180@01))
                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
    ($Perm.min
      (ite
        ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
        $Perm.Write
        $Perm.No)
      (- (- $k@277@01 (pTaken@279@01 r)) (pTaken@280@01 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
;(set-option :timeout 10)
 (set-option :rlimit 26402) (check-sat) 
; unknown
; Constrain original permissions $k@277@01
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (not
        (=
          (ite
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (< (mod (inv@267@01 r) step@180@01) N@179@01)))
            (/ (to_real 1) (to_real 4))
            $Perm.No)
          $Perm.No))
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (< (mod (inv@267@01 r) step@180@01) N@179@01)))
        (<
          (ite
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            $k@277@01
            $Perm.No)
          (/ (to_real 1) (to_real 4)))
        (<
          (ite
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            $k@277@01
            $Perm.No)
          $Perm.No)))
    :pattern ((inv@267@01 r))
    :qid |qp.srp41|))
  (forall ((r $Ref)) (!
    (implies
      (not
        (=
          (ite
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (< (mod (inv@267@01 r) step@180@01) N@179@01)))
            (/ (to_real 1) (to_real 4))
            $Perm.No)
          $Perm.No))
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (< (mod (inv@267@01 r) step@180@01) N@179@01)))
        (<
          (ite
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            $k@277@01
            $Perm.No)
          (/ (to_real 1) (to_real 4)))
        (<
          (ite
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            $k@277@01
            $Perm.No)
          $Perm.No)))
    :pattern ((inv@278@01 r))
    :qid |qp.srp41|))))
; Intermediate check if already taken enough permissions
;(set-option :timeout 500)
(push) ; 7
(assert (not (forall ((r $Ref)) (!
  (implies
    (and
      (<= 0 (inv@278@01 r))
      (implies
        (<= 0 (inv@278@01 r))
        (and
          (< (inv@278@01 r) (* M@178@01 step@180@01))
          (implies
            (< (inv@278@01 r) (* M@178@01 step@180@01))
            (and
              (<= 0 (mod (inv@278@01 r) step@180@01))
              (implies
                (<= 0 (mod (inv@278@01 r) step@180@01))
                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
    (= (- $k@277@01 (pTaken@279@01 r)) $Perm.No))
  
  ))))
 (set-option :rlimit 38360) (check-sat) 
; unsat
(pop) ; 7
; 0.03s
; 
; Final check if taken enough permissions
; Done removing quantified permissions
(declare-const sm@282@01 $FVF<Int>)
; Definitional axioms for SM domain
(assert (forall ((r $Ref)) (!
  (iff
    (Set_in r ($FVF.domain_Ref__Integer_value (as sm@282@01  $FVF<Int>)))
    (and
      (and
        (<= 0 (inv@278@01 r))
        (implies
          (<= 0 (inv@278@01 r))
          (and
            (< (inv@278@01 r) (* M@178@01 step@180@01))
            (implies
              (< (inv@278@01 r) (* M@178@01 step@180@01))
              (and
                (<= 0 (mod (inv@278@01 r) step@180@01))
                (implies
                  (<= 0 (mod (inv@278@01 r) step@180@01))
                  (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
      (< $Perm.No $k@277@01)))
  :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@282@01  $FVF<Int>))))
  :qid |qp.fvfDomDef45|)))
; Definitional axioms for SM values
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@278@01 r))
            (implies
              (<= 0 (inv@278@01 r))
              (and
                (< (inv@278@01 r) (* M@178@01 step@180@01))
                (implies
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (and
                    (<= 0 (mod (inv@278@01 r) step@180@01))
                    (implies
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
          (< $Perm.No $k@277@01))
        ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
    :qid |qp.fvfValDef42|))
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@278@01 r))
            (implies
              (<= 0 (inv@278@01 r))
              (and
                (< (inv@278@01 r) (* M@178@01 step@180@01))
                (implies
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (and
                    (<= 0 (mod (inv@278@01 r) step@180@01))
                    (implies
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
          (< $Perm.No $k@277@01))
        ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
    :qid |qp.fvfValDef42|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@278@01 r))
            (implies
              (<= 0 (inv@278@01 r))
              (and
                (< (inv@278@01 r) (* M@178@01 step@180@01))
                (implies
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (and
                    (<= 0 (mod (inv@278@01 r) step@180@01))
                    (implies
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
          (< $Perm.No $k@277@01))
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (< (mod (inv@267@01 r) step@180@01) N@179@01))))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
    :qid |qp.fvfValDef43|))
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@278@01 r))
            (implies
              (<= 0 (inv@278@01 r))
              (and
                (< (inv@278@01 r) (* M@178@01 step@180@01))
                (implies
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (and
                    (<= 0 (mod (inv@278@01 r) step@180@01))
                    (implies
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
          (< $Perm.No $k@277@01))
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (< (mod (inv@267@01 r) step@180@01) N@179@01))))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
    :qid |qp.fvfValDef43|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@278@01 r))
            (implies
              (<= 0 (inv@278@01 r))
              (and
                (< (inv@278@01 r) (* M@178@01 step@180@01))
                (implies
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (and
                    (<= 0 (mod (inv@278@01 r) step@180@01))
                    (implies
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
          (< $Perm.No $k@277@01))
        (<
          $Perm.No
          (-
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@196@01 r))
                  (< (mod (inv@196@01 r) step@180@01) N@179@01)))
              (/ (to_real 1) (to_real 2))
              $Perm.No)
            (pTaken@252@01 r))))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
    :qid |qp.fvfValDef44|))
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (and
            (<= 0 (inv@278@01 r))
            (implies
              (<= 0 (inv@278@01 r))
              (and
                (< (inv@278@01 r) (* M@178@01 step@180@01))
                (implies
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (and
                    (<= 0 (mod (inv@278@01 r) step@180@01))
                    (implies
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
          (< $Perm.No $k@277@01))
        (<
          $Perm.No
          (-
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@196@01 r))
                  (< (mod (inv@196@01 r) step@180@01) N@179@01)))
              (/ (to_real 1) (to_real 2))
              $Perm.No)
            (pTaken@252@01 r))))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef44|))))
(pop) ; 6
; Joined path conditions
(assert (and
  (and
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@277@01))
          (<
            $Perm.No
            (-
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@196@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                (/ (to_real 1) (to_real 2))
                $Perm.No)
              (pTaken@252@01 r))))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
      :qid |qp.fvfValDef44|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@277@01))
          (<
            $Perm.No
            (-
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@196@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                (/ (to_real 1) (to_real 2))
                $Perm.No)
              (pTaken@252@01 r))))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
      :qid |qp.fvfValDef44|)))
  (and
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@277@01))
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (< (mod (inv@267@01 r) step@180@01) N@179@01))))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
      :qid |qp.fvfValDef43|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@277@01))
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (< (mod (inv@267@01 r) step@180@01) N@179@01))))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
      :qid |qp.fvfValDef43|)))
  (and
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@277@01))
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r)))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
      :qid |qp.fvfValDef42|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@277@01))
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r)))
        (=
          ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
          ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
      :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
      :qid |qp.fvfValDef42|)))
  (forall ((r $Ref)) (!
    (iff
      (Set_in r ($FVF.domain_Ref__Integer_value (as sm@282@01  $FVF<Int>)))
      (and
        (and
          (<= 0 (inv@278@01 r))
          (implies
            (<= 0 (inv@278@01 r))
            (and
              (< (inv@278@01 r) (* M@178@01 step@180@01))
              (implies
                (< (inv@278@01 r) (* M@178@01 step@180@01))
                (and
                  (<= 0 (mod (inv@278@01 r) step@180@01))
                  (implies
                    (<= 0 (mod (inv@278@01 r) step@180@01))
                    (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
        (< $Perm.No $k@277@01)))
    :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@282@01  $FVF<Int>))))
    :qid |qp.fvfDomDef45|))
  (and
    (forall ((r $Ref)) (!
      (implies
        (not
          (=
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (< (mod (inv@267@01 r) step@180@01) N@179@01)))
              (/ (to_real 1) (to_real 4))
              $Perm.No)
            $Perm.No))
        (ite
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (< (mod (inv@267@01 r) step@180@01) N@179@01)))
          (<
            (ite
              (and
                (<= 0 (inv@278@01 r))
                (implies
                  (<= 0 (inv@278@01 r))
                  (and
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
              $k@277@01
              $Perm.No)
            (/ (to_real 1) (to_real 4)))
          (<
            (ite
              (and
                (<= 0 (inv@278@01 r))
                (implies
                  (<= 0 (inv@278@01 r))
                  (and
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
              $k@277@01
              $Perm.No)
            $Perm.No)))
      :pattern ((inv@267@01 r))
      :qid |qp.srp41|))
    (forall ((r $Ref)) (!
      (implies
        (not
          (=
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (< (mod (inv@267@01 r) step@180@01) N@179@01)))
              (/ (to_real 1) (to_real 4))
              $Perm.No)
            $Perm.No))
        (ite
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (< (mod (inv@267@01 r) step@180@01) N@179@01)))
          (<
            (ite
              (and
                (<= 0 (inv@278@01 r))
                (implies
                  (<= 0 (inv@278@01 r))
                  (and
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
              $k@277@01
              $Perm.No)
            (/ (to_real 1) (to_real 4)))
          (<
            (ite
              (and
                (<= 0 (inv@278@01 r))
                (implies
                  (<= 0 (inv@278@01 r))
                  (and
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
              $k@277@01
              $Perm.No)
            $Perm.No)))
      :pattern ((inv@278@01 r))
      :qid |qp.srp41|)))
  (forall ((r $Ref)) (!
    (implies
      (and
        (and
          (<= 0 (inv@278@01 r))
          (implies
            (<= 0 (inv@278@01 r))
            (and
              (< (inv@278@01 r) (* M@178@01 step@180@01))
              (implies
                (< (inv@278@01 r) (* M@178@01 step@180@01))
                (and
                  (<= 0 (mod (inv@278@01 r) step@180@01))
                  (implies
                    (<= 0 (mod (inv@278@01 r) step@180@01))
                    (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
        (< $Perm.No $k@277@01))
      (= ($Seq.index matrix@181@01 (inv@278@01 r)) r))
    :pattern ((inv@278@01 r))
    :qid |Ref__Integer_value-fctOfInv|))
  (forall ((k@273@01 Int)) (!
    (implies
      (and
        (and
          (<= 0 k@273@01)
          (implies
            (<= 0 k@273@01)
            (and
              (< k@273@01 (* M@178@01 step@180@01))
              (implies
                (< k@273@01 (* M@178@01 step@180@01))
                (and
                  (<= 0 (mod k@273@01 step@180@01))
                  (implies
                    (<= 0 (mod k@273@01 step@180@01))
                    (< (mod k@273@01 step@180@01) N@179@01)))))))
        (< $Perm.No $k@277@01))
      (= (inv@278@01 ($Seq.index matrix@181@01 k@273@01)) k@273@01))
    :pattern (($Seq.index matrix@181@01 k@273@01))
    :qid |Ref__Integer_value-invOfFct|))
  (forall ((k@273@01 Int)) (!
    ($Perm.isReadVar $k@277@01 $Perm.Write)
    :pattern (($Seq.index matrix@181@01 k@273@01))
    :qid |Ref__Integer_value-aux|))
  (<= 0 (* M@178@01 step@180@01))
  (> step@180@01 0)
  (<= 0 N@179@01)))
(pop) ; 5
(push) ; 5
; [else-branch: 31 | !k@271@01 in [0..P@182@01]]
(assert (not ($Seq.contains ($Seq.range 0 P@182@01) k@271@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (implies
  ($Seq.contains ($Seq.range 0 P@182@01) k@271@01)
  (and
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@278@01 r))
                  (implies
                    (<= 0 (inv@278@01 r))
                    (and
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (implies
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (and
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (implies
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                (< $Perm.No $k@277@01))
              (<
                $Perm.No
                (-
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@196@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@196@01 r))
                        (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                    (/ (to_real 1) (to_real 2))
                    $Perm.No)
                  (pTaken@252@01 r))))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
          :qid |qp.fvfValDef44|))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@278@01 r))
                  (implies
                    (<= 0 (inv@278@01 r))
                    (and
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (implies
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (and
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (implies
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                (< $Perm.No $k@277@01))
              (<
                $Perm.No
                (-
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@196@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@196@01 r))
                        (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                    (/ (to_real 1) (to_real 2))
                    $Perm.No)
                  (pTaken@252@01 r))))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef44|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@278@01 r))
                  (implies
                    (<= 0 (inv@278@01 r))
                    (and
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (implies
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (and
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (implies
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                (< $Perm.No $k@277@01))
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (< (mod (inv@267@01 r) step@180@01) N@179@01))))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
          :qid |qp.fvfValDef43|))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@278@01 r))
                  (implies
                    (<= 0 (inv@278@01 r))
                    (and
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (implies
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (and
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (implies
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                (< $Perm.No $k@277@01))
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (< (mod (inv@267@01 r) step@180@01) N@179@01))))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
          :qid |qp.fvfValDef43|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@278@01 r))
                  (implies
                    (<= 0 (inv@278@01 r))
                    (and
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (implies
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (and
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (implies
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                (< $Perm.No $k@277@01))
              ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
          :qid |qp.fvfValDef42|))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (and
                  (<= 0 (inv@278@01 r))
                  (implies
                    (<= 0 (inv@278@01 r))
                    (and
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (implies
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (and
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (implies
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                (< $Perm.No $k@277@01))
              ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
          :qid |qp.fvfValDef42|)))
      (forall ((r $Ref)) (!
        (iff
          (Set_in r ($FVF.domain_Ref__Integer_value (as sm@282@01  $FVF<Int>)))
          (and
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@277@01)))
        :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@282@01  $FVF<Int>))))
        :qid |qp.fvfDomDef45|))
      (and
        (forall ((r $Ref)) (!
          (implies
            (not
              (=
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@267@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@267@01 r))
                      (< (mod (inv@267@01 r) step@180@01) N@179@01)))
                  (/ (to_real 1) (to_real 4))
                  $Perm.No)
                $Perm.No))
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (< (mod (inv@267@01 r) step@180@01) N@179@01)))
              (<
                (ite
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  $k@277@01
                  $Perm.No)
                (/ (to_real 1) (to_real 4)))
              (<
                (ite
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  $k@277@01
                  $Perm.No)
                $Perm.No)))
          :pattern ((inv@267@01 r))
          :qid |qp.srp41|))
        (forall ((r $Ref)) (!
          (implies
            (not
              (=
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@267@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@267@01 r))
                      (< (mod (inv@267@01 r) step@180@01) N@179@01)))
                  (/ (to_real 1) (to_real 4))
                  $Perm.No)
                $Perm.No))
            (ite
              (and
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (implies
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (< (mod (inv@267@01 r) step@180@01) N@179@01)))
              (<
                (ite
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  $k@277@01
                  $Perm.No)
                (/ (to_real 1) (to_real 4)))
              (<
                (ite
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  $k@277@01
                  $Perm.No)
                $Perm.No)))
          :pattern ((inv@278@01 r))
          :qid |qp.srp41|)))
      (forall ((r $Ref)) (!
        (implies
          (and
            (and
              (<= 0 (inv@278@01 r))
              (implies
                (<= 0 (inv@278@01 r))
                (and
                  (< (inv@278@01 r) (* M@178@01 step@180@01))
                  (implies
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod (inv@278@01 r) step@180@01))
                      (implies
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
            (< $Perm.No $k@277@01))
          (= ($Seq.index matrix@181@01 (inv@278@01 r)) r))
        :pattern ((inv@278@01 r))
        :qid |Ref__Integer_value-fctOfInv|))
      (forall ((k@273@01 Int)) (!
        (implies
          (and
            (and
              (<= 0 k@273@01)
              (implies
                (<= 0 k@273@01)
                (and
                  (< k@273@01 (* M@178@01 step@180@01))
                  (implies
                    (< k@273@01 (* M@178@01 step@180@01))
                    (and
                      (<= 0 (mod k@273@01 step@180@01))
                      (implies
                        (<= 0 (mod k@273@01 step@180@01))
                        (< (mod k@273@01 step@180@01) N@179@01)))))))
            (< $Perm.No $k@277@01))
          (= (inv@278@01 ($Seq.index matrix@181@01 k@273@01)) k@273@01))
        :pattern (($Seq.index matrix@181@01 k@273@01))
        :qid |Ref__Integer_value-invOfFct|))
      (forall ((k@273@01 Int)) (!
        ($Perm.isReadVar $k@277@01 $Perm.Write)
        :pattern (($Seq.index matrix@181@01 k@273@01))
        :qid |Ref__Integer_value-aux|))
      (<= 0 (* M@178@01 step@180@01))
      (> step@180@01 0)
      (<= 0 N@179@01))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
        :qid |qp.fvfValDef34|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
        :qid |qp.fvfValDef34|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
        :qid |qp.fvfValDef33|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
        :qid |qp.fvfValDef33|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (<
            $Perm.No
            (-
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@196@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                (/ (to_real 1) (to_real 2))
                $Perm.No)
              (pTaken@252@01 r)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
        :qid |qp.fvfValDef40|))
      (forall ((r $Ref)) (!
        (implies
          (<
            $Perm.No
            (-
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@196@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                (/ (to_real 1) (to_real 2))
                $Perm.No)
              (pTaken@252@01 r)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
        :qid |qp.fvfValDef40|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (< (mod (inv@267@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
        :qid |qp.fvfValDef39|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (< (mod (inv@267@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
        :qid |qp.fvfValDef39|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
        :qid |qp.fvfValDef38|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
        :qid |qp.fvfValDef38|)))
    ($Seq.contains ($Seq.range 0 P@182@01) k@271@01))))
; Joined path conditions
; [eval] hist[k]
;(set-option :timeout 0)
(push) ; 4
(assert (not (>= k@271@01 0)))
 (set-option :rlimit 170289) (check-sat) 
; unknown
(pop) ; 4
; 0.01s
; 
(pop) ; 3
; Nested auxiliary terms
(assert (forall ((k@271@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@271@01)
    (and
      (and
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                (<
                  $Perm.No
                  (-
                    (ite
                      (and
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@196@01 r))
                        (implies
                          ($Seq.contains
                            ($Seq.range 0 (* M@178@01 step@180@01))
                            (inv@196@01 r))
                          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                      (/ (to_real 1) (to_real 2))
                      $Perm.No)
                    (pTaken@252@01 r))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
            :qid |qp.fvfValDef44|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                (<
                  $Perm.No
                  (-
                    (ite
                      (and
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@196@01 r))
                        (implies
                          ($Seq.contains
                            ($Seq.range 0 (* M@178@01 step@180@01))
                            (inv@196@01 r))
                          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                      (/ (to_real 1) (to_real 2))
                      $Perm.No)
                    (pTaken@252@01 r))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
            :qid |qp.fvfValDef44|)))
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@267@01 r))
                    (< (mod (inv@267@01 r) step@180@01) N@179@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
            :qid |qp.fvfValDef43|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@267@01 r))
                    (< (mod (inv@267@01 r) step@180@01) N@179@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
            :qid |qp.fvfValDef43|)))
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
            :qid |qp.fvfValDef42|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
            :qid |qp.fvfValDef42|)))
        (forall ((r $Ref)) (!
          (iff
            (Set_in r ($FVF.domain_Ref__Integer_value (as sm@282@01  $FVF<Int>)))
            (and
              (and
                (<= 0 (inv@278@01 r))
                (implies
                  (<= 0 (inv@278@01 r))
                  (and
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
              (< $Perm.No $k@277@01)))
          :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@282@01  $FVF<Int>))))
          :qid |qp.fvfDomDef45|))
        (and
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@267@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@267@01 r))
                        (< (mod (inv@267@01 r) step@180@01) N@179@01)))
                    (/ (to_real 1) (to_real 4))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@267@01 r))
                    (< (mod (inv@267@01 r) step@180@01) N@179@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@278@01 r))
                      (implies
                        (<= 0 (inv@278@01 r))
                        (and
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@278@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@278@01 r) step@180@01))
                                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                    $k@277@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 4)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@278@01 r))
                      (implies
                        (<= 0 (inv@278@01 r))
                        (and
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@278@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@278@01 r) step@180@01))
                                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                    $k@277@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@267@01 r))
            :qid |qp.srp41|))
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@267@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@267@01 r))
                        (< (mod (inv@267@01 r) step@180@01) N@179@01)))
                    (/ (to_real 1) (to_real 4))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@267@01 r))
                    (< (mod (inv@267@01 r) step@180@01) N@179@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@278@01 r))
                      (implies
                        (<= 0 (inv@278@01 r))
                        (and
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@278@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@278@01 r) step@180@01))
                                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                    $k@277@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 4)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@278@01 r))
                      (implies
                        (<= 0 (inv@278@01 r))
                        (and
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@278@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@278@01 r) step@180@01))
                                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                    $k@277@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@278@01 r))
            :qid |qp.srp41|)))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (<= 0 (inv@278@01 r))
                (implies
                  (<= 0 (inv@278@01 r))
                  (and
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
              (< $Perm.No $k@277@01))
            (= ($Seq.index matrix@181@01 (inv@278@01 r)) r))
          :pattern ((inv@278@01 r))
          :qid |Ref__Integer_value-fctOfInv|))
        (forall ((k@273@01 Int)) (!
          (implies
            (and
              (and
                (<= 0 k@273@01)
                (implies
                  (<= 0 k@273@01)
                  (and
                    (< k@273@01 (* M@178@01 step@180@01))
                    (implies
                      (< k@273@01 (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod k@273@01 step@180@01))
                        (implies
                          (<= 0 (mod k@273@01 step@180@01))
                          (< (mod k@273@01 step@180@01) N@179@01)))))))
              (< $Perm.No $k@277@01))
            (= (inv@278@01 ($Seq.index matrix@181@01 k@273@01)) k@273@01))
          :pattern (($Seq.index matrix@181@01 k@273@01))
          :qid |Ref__Integer_value-invOfFct|))
        (forall ((k@273@01 Int)) (!
          ($Perm.isReadVar $k@277@01 $Perm.Write)
          :pattern (($Seq.index matrix@181@01 k@273@01))
          :qid |Ref__Integer_value-aux|))
        (<= 0 (* M@178@01 step@180@01))
        (> step@180@01 0)
        (<= 0 N@179@01))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef34|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef34|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef33|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
          :qid |qp.fvfValDef33|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (<
              $Perm.No
              (-
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@196@01 r))
                      (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                  (/ (to_real 1) (to_real 2))
                  $Perm.No)
                (pTaken@252@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
          :qid |qp.fvfValDef40|))
        (forall ((r $Ref)) (!
          (implies
            (<
              $Perm.No
              (-
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@196@01 r))
                      (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                  (/ (to_real 1) (to_real 2))
                  $Perm.No)
                (pTaken@252@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef40|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (< (mod (inv@267@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
          :qid |qp.fvfValDef39|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (< (mod (inv@267@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
          :qid |qp.fvfValDef39|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
          :qid |qp.fvfValDef38|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
          :qid |qp.fvfValDef38|)))
      ($Seq.contains ($Seq.range 0 P@182@01) k@271@01)))
  :pattern (($Seq.contains ($Seq.range 0 P@182@01) k@271@01))
  :qid |prog.l88-aux|)))
(assert (forall ((k@271@01 Int)) (!
  (implies
    ($Seq.contains ($Seq.range 0 P@182@01) k@271@01)
    (and
      (and
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                (<
                  $Perm.No
                  (-
                    (ite
                      (and
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@196@01 r))
                        (implies
                          ($Seq.contains
                            ($Seq.range 0 (* M@178@01 step@180@01))
                            (inv@196@01 r))
                          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                      (/ (to_real 1) (to_real 2))
                      $Perm.No)
                    (pTaken@252@01 r))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
            :qid |qp.fvfValDef44|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                (<
                  $Perm.No
                  (-
                    (ite
                      (and
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@196@01 r))
                        (implies
                          ($Seq.contains
                            ($Seq.range 0 (* M@178@01 step@180@01))
                            (inv@196@01 r))
                          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                      (/ (to_real 1) (to_real 2))
                      $Perm.No)
                    (pTaken@252@01 r))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
            :qid |qp.fvfValDef44|)))
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@267@01 r))
                    (< (mod (inv@267@01 r) step@180@01) N@179@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
            :qid |qp.fvfValDef43|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@267@01 r))
                    (< (mod (inv@267@01 r) step@180@01) N@179@01))))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
            :qid |qp.fvfValDef43|)))
        (and
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r))
            :qid |qp.fvfValDef42|))
          (forall ((r $Ref)) (!
            (implies
              (and
                (and
                  (and
                    (<= 0 (inv@278@01 r))
                    (implies
                      (<= 0 (inv@278@01 r))
                      (and
                        (< (inv@278@01 r) (* M@178@01 step@180@01))
                        (implies
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (and
                            (<= 0 (mod (inv@278@01 r) step@180@01))
                            (implies
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                  (< $Perm.No $k@277@01))
                ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r)))
              (=
                ($FVF.lookup_Ref__Integer_value (as sm@282@01  $FVF<Int>) r)
                ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
            :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
            :qid |qp.fvfValDef42|)))
        (forall ((r $Ref)) (!
          (iff
            (Set_in r ($FVF.domain_Ref__Integer_value (as sm@282@01  $FVF<Int>)))
            (and
              (and
                (<= 0 (inv@278@01 r))
                (implies
                  (<= 0 (inv@278@01 r))
                  (and
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
              (< $Perm.No $k@277@01)))
          :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (as sm@282@01  $FVF<Int>))))
          :qid |qp.fvfDomDef45|))
        (and
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@267@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@267@01 r))
                        (< (mod (inv@267@01 r) step@180@01) N@179@01)))
                    (/ (to_real 1) (to_real 4))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@267@01 r))
                    (< (mod (inv@267@01 r) step@180@01) N@179@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@278@01 r))
                      (implies
                        (<= 0 (inv@278@01 r))
                        (and
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@278@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@278@01 r) step@180@01))
                                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                    $k@277@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 4)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@278@01 r))
                      (implies
                        (<= 0 (inv@278@01 r))
                        (and
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@278@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@278@01 r) step@180@01))
                                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                    $k@277@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@267@01 r))
            :qid |qp.srp41|))
          (forall ((r $Ref)) (!
            (implies
              (not
                (=
                  (ite
                    (and
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@267@01 r))
                      (implies
                        ($Seq.contains
                          ($Seq.range 0 (* M@178@01 step@180@01))
                          (inv@267@01 r))
                        (< (mod (inv@267@01 r) step@180@01) N@179@01)))
                    (/ (to_real 1) (to_real 4))
                    $Perm.No)
                  $Perm.No))
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@267@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@267@01 r))
                    (< (mod (inv@267@01 r) step@180@01) N@179@01)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@278@01 r))
                      (implies
                        (<= 0 (inv@278@01 r))
                        (and
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@278@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@278@01 r) step@180@01))
                                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                    $k@277@01
                    $Perm.No)
                  (/ (to_real 1) (to_real 4)))
                (<
                  (ite
                    (and
                      (<= 0 (inv@278@01 r))
                      (implies
                        (<= 0 (inv@278@01 r))
                        (and
                          (< (inv@278@01 r) (* M@178@01 step@180@01))
                          (implies
                            (< (inv@278@01 r) (* M@178@01 step@180@01))
                            (and
                              (<= 0 (mod (inv@278@01 r) step@180@01))
                              (implies
                                (<= 0 (mod (inv@278@01 r) step@180@01))
                                (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
                    $k@277@01
                    $Perm.No)
                  $Perm.No)))
            :pattern ((inv@278@01 r))
            :qid |qp.srp41|)))
        (forall ((r $Ref)) (!
          (implies
            (and
              (and
                (<= 0 (inv@278@01 r))
                (implies
                  (<= 0 (inv@278@01 r))
                  (and
                    (< (inv@278@01 r) (* M@178@01 step@180@01))
                    (implies
                      (< (inv@278@01 r) (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod (inv@278@01 r) step@180@01))
                        (implies
                          (<= 0 (mod (inv@278@01 r) step@180@01))
                          (< (mod (inv@278@01 r) step@180@01) N@179@01)))))))
              (< $Perm.No $k@277@01))
            (= ($Seq.index matrix@181@01 (inv@278@01 r)) r))
          :pattern ((inv@278@01 r))
          :qid |Ref__Integer_value-fctOfInv|))
        (forall ((k@273@01 Int)) (!
          (implies
            (and
              (and
                (<= 0 k@273@01)
                (implies
                  (<= 0 k@273@01)
                  (and
                    (< k@273@01 (* M@178@01 step@180@01))
                    (implies
                      (< k@273@01 (* M@178@01 step@180@01))
                      (and
                        (<= 0 (mod k@273@01 step@180@01))
                        (implies
                          (<= 0 (mod k@273@01 step@180@01))
                          (< (mod k@273@01 step@180@01) N@179@01)))))))
              (< $Perm.No $k@277@01))
            (= (inv@278@01 ($Seq.index matrix@181@01 k@273@01)) k@273@01))
          :pattern (($Seq.index matrix@181@01 k@273@01))
          :qid |Ref__Integer_value-invOfFct|))
        (forall ((k@273@01 Int)) (!
          ($Perm.isReadVar $k@277@01 $Perm.Write)
          :pattern (($Seq.index matrix@181@01 k@273@01))
          :qid |Ref__Integer_value-aux|))
        (<= 0 (* M@178@01 step@180@01))
        (> step@180@01 0)
        (<= 0 N@179@01))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef34|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef34|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef33|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
          :qid |qp.fvfValDef33|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (<
              $Perm.No
              (-
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@196@01 r))
                      (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                  (/ (to_real 1) (to_real 2))
                  $Perm.No)
                (pTaken@252@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
          :qid |qp.fvfValDef40|))
        (forall ((r $Ref)) (!
          (implies
            (<
              $Perm.No
              (-
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@196@01 r))
                      (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                  (/ (to_real 1) (to_real 2))
                  $Perm.No)
                (pTaken@252@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef40|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (< (mod (inv@267@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
          :qid |qp.fvfValDef39|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (< (mod (inv@267@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
          :qid |qp.fvfValDef39|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
          :qid |qp.fvfValDef38|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
          :qid |qp.fvfValDef38|)))
      ($Seq.contains ($Seq.range 0 P@182@01) k@271@01)))
  :pattern ()
  :qid |prog.l88-aux|)))
(assert (and
  (forall ((k@271@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) k@271@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) ($Seq.index
          hist@183@01
          k@271@01))
        (+
          ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) ($Seq.index
            hist@183@01
            k@271@01))
          (count_square ($Snap.combine
            $Snap.unit
            ($Snap.combine
              $Snap.unit
              ($Snap.combine
                $Snap.unit
                ($Snap.combine
                  $Snap.unit
                  ($Snap.combine
                    $Snap.unit
                    ($Snap.combine
                      $Snap.unit
                      ($Snap.combine
                        $Snap.unit
                        ($Snap.combine
                          $Snap.unit
                          ($SortWrappers.$FVF<Int>To$Snap (as sm@282@01  $FVF<Int>)))))))))) 0 0 N@179@01 step@180@01 0 (*
            M@178@01
            step@180@01) matrix@181@01 k@271@01))))
    :pattern (($Seq.contains ($Seq.range 0 P@182@01) k@271@01))
    :qid |prog.l88|))
  (forall ((k@271@01 Int)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) k@271@01)
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) ($Seq.index
          hist@183@01
          k@271@01))
        (+
          ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) ($Seq.index
            hist@183@01
            k@271@01))
          (count_square ($Snap.combine
            $Snap.unit
            ($Snap.combine
              $Snap.unit
              ($Snap.combine
                $Snap.unit
                ($Snap.combine
                  $Snap.unit
                  ($Snap.combine
                    $Snap.unit
                    ($Snap.combine
                      $Snap.unit
                      ($Snap.combine
                        $Snap.unit
                        ($Snap.combine
                          $Snap.unit
                          ($SortWrappers.$FVF<Int>To$Snap (as sm@282@01  $FVF<Int>)))))))))) 0 0 N@179@01 step@180@01 0 (*
            M@178@01
            step@180@01) matrix@181@01 k@271@01))))
    :pattern ()
    :qid |prog.l88|))))
; [eval] N <= step
; [eval] (forall k_fresh_rw_0: Int :: { matrix[k_fresh_rw_0] } (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> matrix[k_fresh_rw_0].Ref__Integer_value == old(matrix[k_fresh_rw_0].Ref__Integer_value))
(declare-const k_fresh_rw_0@283@01 Int)
(push) ; 3
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N ==> matrix[k_fresh_rw_0].Ref__Integer_value == old(matrix[k_fresh_rw_0].Ref__Integer_value)
; [eval] (k_fresh_rw_0 in [0..M * step)) && k_fresh_rw_0 % step < N
; [eval] (k_fresh_rw_0 in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@284@01 ==> k_fresh_rw_0 % step < N
(push) ; 4
; [then-branch: 35 | k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01] | live]
; [else-branch: 35 | !k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01] | live]
(push) ; 5
; [then-branch: 35 | k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@283@01))
; [eval] k_fresh_rw_0 % step < N
; [eval] k_fresh_rw_0 % step
(push) ; 6
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 2920) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(pop) ; 5
(push) ; 5
; [else-branch: 35 | !k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@283@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(push) ; 4
; [then-branch: 36 | k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@283@01 % step@180@01 < N@179@01 | live]
; [else-branch: 36 | !k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@283@01 % step@180@01 < N@179@01 | live]
(push) ; 5
; [then-branch: 36 | k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@283@01 % step@180@01 < N@179@01]
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@283@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@283@01)
    (< (mod k_fresh_rw_0@283@01 step@180@01) N@179@01))))
; [eval] matrix[k_fresh_rw_0].Ref__Integer_value == old(matrix[k_fresh_rw_0].Ref__Integer_value)
; [eval] matrix[k_fresh_rw_0]
(push) ; 6
(assert (not (>= k_fresh_rw_0@283@01 0)))
 (set-option :rlimit 9846) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k_fresh_rw_0@283@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 3845) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        ($Seq.contains
          ($Seq.range 0 P@182@01)
          (inv@270@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01)))
        $Perm.Write
        $Perm.No)
      (ite
        (and
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            (inv@267@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01)))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01)))
            (<
              (mod
                (inv@267@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01))
                step@180@01)
              N@179@01)))
        (/ (to_real 1) (to_real 4))
        $Perm.No))
    (-
      (ite
        (and
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01)))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01)))
            (<
              (mod
                (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01))
                step@180@01)
              N@179@01)))
        (/ (to_real 1) (to_real 2))
        $Perm.No)
      (pTaken@252@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01)))))))
 (set-option :rlimit 16945) (check-sat) 
; unsat
(pop) ; 6
; 0.06s
; 
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
    :qid |qp.fvfValDef38|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
    :qid |qp.fvfValDef38|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
          (< (mod (inv@267@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
    :qid |qp.fvfValDef39|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
          (< (mod (inv@267@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
    :qid |qp.fvfValDef39|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (<
        $Perm.No
        (-
          (ite
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (/ (to_real 1) (to_real 2))
            $Perm.No)
          (pTaken@252@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
    :qid |qp.fvfValDef40|))
  (forall ((r $Ref)) (!
    (implies
      (<
        $Perm.No
        (-
          (ite
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (/ (to_real 1) (to_real 2))
            $Perm.No)
          (pTaken@252@01 r)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef40|))))
; [eval] old(matrix[k_fresh_rw_0].Ref__Integer_value)
; [eval] matrix[k_fresh_rw_0]
(push) ; 6
(assert (not (>= k_fresh_rw_0@283@01 0)))
 (set-option :rlimit 46377) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (< k_fresh_rw_0@283@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 25040) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      ($Seq.contains
        ($Seq.range 0 P@182@01)
        (inv@241@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01)))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01)))
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01)))
          (<
            (mod
              (inv@196@01 ($Seq.index matrix@181@01 k_fresh_rw_0@283@01))
              step@180@01)
            N@179@01)))
      (/ (to_real 1) (to_real 2))
      $Perm.No)))))
 (set-option :rlimit 41581) (check-sat) 
; unsat
(pop) ; 6
; 0.05s
; 
(assert (and
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
    :qid |qp.fvfValDef33|))
  (forall ((r $Ref)) (!
    (implies
      ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
    :qid |qp.fvfValDef33|))))
(assert (and
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
    :qid |qp.fvfValDef34|))
  (forall ((r $Ref)) (!
    (implies
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@196@01 r))
          (< (mod (inv@196@01 r) step@180@01) N@179@01)))
      (=
        ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
        ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
    :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
    :qid |qp.fvfValDef34|))))
(pop) ; 5
(push) ; 5
; [else-branch: 36 | !k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01] && k_fresh_rw_0@283@01 in [0..M@178@01 * step@180@01] ==> k_fresh_rw_0@283@01 % step@180@01 < N@179@01]
(assert (not
  (and
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@283@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@283@01)
      (< (mod k_fresh_rw_0@283@01 step@180@01) N@179@01)))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
(assert (implies
  (and
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@283@01)
    (implies
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@283@01)
      (< (mod k_fresh_rw_0@283@01 step@180@01) N@179@01)))
  (and
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
        :qid |qp.fvfValDef34|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
        :qid |qp.fvfValDef34|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
        :qid |qp.fvfValDef33|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
        :qid |qp.fvfValDef33|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (<
            $Perm.No
            (-
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@196@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                (/ (to_real 1) (to_real 2))
                $Perm.No)
              (pTaken@252@01 r)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
        :qid |qp.fvfValDef40|))
      (forall ((r $Ref)) (!
        (implies
          (<
            $Perm.No
            (-
              (ite
                (and
                  ($Seq.contains
                    ($Seq.range 0 (* M@178@01 step@180@01))
                    (inv@196@01 r))
                  (implies
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                (/ (to_real 1) (to_real 2))
                $Perm.No)
              (pTaken@252@01 r)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
        :qid |qp.fvfValDef40|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (< (mod (inv@267@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
        :qid |qp.fvfValDef39|))
      (forall ((r $Ref)) (!
        (implies
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (< (mod (inv@267@01 r) step@180@01) N@179@01)))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
        :qid |qp.fvfValDef39|)))
    (and
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
        :qid |qp.fvfValDef38|))
      (forall ((r $Ref)) (!
        (implies
          ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
          (=
            ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
            ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
        :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
        :qid |qp.fvfValDef38|)))
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@283@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@283@01)
        (< (mod k_fresh_rw_0@283@01 step@180@01) N@179@01))))))
; Joined path conditions
(pop) ; 3
; Nested auxiliary terms
(assert (forall ((k_fresh_rw_0@283@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@283@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@283@01)
        (< (mod k_fresh_rw_0@283@01 step@180@01) N@179@01)))
    (and
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef34|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@196@01 r))
                (< (mod (inv@196@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef34|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r))
          :qid |qp.fvfValDef33|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@241@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@239@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@239@01 r))
          :qid |qp.fvfValDef33|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (<
              $Perm.No
              (-
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@196@01 r))
                      (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                  (/ (to_real 1) (to_real 2))
                  $Perm.No)
                (pTaken@252@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
          :qid |qp.fvfValDef40|))
        (forall ((r $Ref)) (!
          (implies
            (<
              $Perm.No
              (-
                (ite
                  (and
                    ($Seq.contains
                      ($Seq.range 0 (* M@178@01 step@180@01))
                      (inv@196@01 r))
                    (implies
                      ($Seq.contains
                        ($Seq.range 0 (* M@178@01 step@180@01))
                        (inv@196@01 r))
                      (< (mod (inv@196@01 r) step@180@01) N@179@01)))
                  (/ (to_real 1) (to_real 2))
                  $Perm.No)
                (pTaken@252@01 r)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@192@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@192@01 r))
          :qid |qp.fvfValDef40|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (< (mod (inv@267@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
          :qid |qp.fvfValDef39|))
        (forall ((r $Ref)) (!
          (implies
            (and
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@267@01 r))
              (implies
                ($Seq.contains
                  ($Seq.range 0 (* M@178@01 step@180@01))
                  (inv@267@01 r))
                (< (mod (inv@267@01 r) step@180@01) N@179@01)))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@263@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@263@01 r))
          :qid |qp.fvfValDef39|)))
      (and
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r))
          :qid |qp.fvfValDef38|))
        (forall ((r $Ref)) (!
          (implies
            ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
            (=
              ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) r)
              ($FVF.lookup_Ref__Integer_value $t@268@01 r)))
          :pattern (($FVF.lookup_Ref__Integer_value $t@268@01 r))
          :qid |qp.fvfValDef38|)))
      (and
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@283@01)
        (implies
          ($Seq.contains
            ($Seq.range 0 (* M@178@01 step@180@01))
            k_fresh_rw_0@283@01)
          (< (mod k_fresh_rw_0@283@01 step@180@01) N@179@01)))))
  :pattern (($Seq.index matrix@181@01 k_fresh_rw_0@283@01))
  :qid |prog.l89-aux|)))
(assert (forall ((k_fresh_rw_0@283@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) k_fresh_rw_0@283@01)
      (implies
        ($Seq.contains
          ($Seq.range 0 (* M@178@01 step@180@01))
          k_fresh_rw_0@283@01)
        (< (mod k_fresh_rw_0@283@01 step@180@01) N@179@01)))
    (=
      ($FVF.lookup_Ref__Integer_value (as sm@272@01  $FVF<Int>) ($Seq.index
        matrix@181@01
        k_fresh_rw_0@283@01))
      ($FVF.lookup_Ref__Integer_value (as sm@243@01  $FVF<Int>) ($Seq.index
        matrix@181@01
        k_fresh_rw_0@283@01))))
  :pattern (($Seq.index matrix@181@01 k_fresh_rw_0@283@01))
  :qid |prog.l89|)))
; State saturation: after contract
;(set-option :timeout 50)
 (set-option :rlimit 3318) (check-sat) 
; unknown
; [eval] M > 0
; [eval] N > 0
; [eval] step >= N
; [eval] P > 0
; [eval] N <= step
(declare-const j1@285@01 Int)
(push) ; 3
; [eval] (j1 in [0..M * step)) && j1 % step < N
; [eval] (j1 in [0..M * step))
; [eval] [0..M * step)
; [eval] M * step
; [eval] v@286@01 ==> j1 % step < N
(push) ; 4
; [then-branch: 37 | j1@285@01 in [0..M@178@01 * step@180@01] | live]
; [else-branch: 37 | !j1@285@01 in [0..M@178@01 * step@180@01] | live]
(push) ; 5
; [then-branch: 37 | j1@285@01 in [0..M@178@01 * step@180@01]]
(assert ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@285@01))
; [eval] j1 % step < N
; [eval] j1 % step
;(set-option :timeout 0)
(push) ; 6
(assert (not (not (= step@180@01 0))))
 (set-option :rlimit 783797) (check-sat) 
; unsat
(pop) ; 6
; 0.00s
; 
(pop) ; 5
(push) ; 5
; [else-branch: 37 | !j1@285@01 in [0..M@178@01 * step@180@01]]
(assert (not ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@285@01)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (and
  ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@285@01)
  (implies
    ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@285@01)
    (< (mod j1@285@01 step@180@01) N@179@01))))
(push) ; 4
(assert (not (not (= 2 0))))
 (set-option :rlimit 149410) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
; [eval] matrix[j1]
(push) ; 4
(assert (not (>= j1@285@01 0)))
 (set-option :rlimit 190960) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(push) ; 4
(assert (not (< j1@285@01 ($Seq.length matrix@181@01))))
 (set-option :rlimit 3140) (check-sat) 
; unsat
(pop) ; 4
; 0.00s
; 
(pop) ; 3
(declare-fun inv@287@01 ($Ref) Int)
; Nested auxiliary terms
(push) ; 3
(assert (not (forall ((j1@285@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@285@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@285@01)
        (< (mod j1@285@01 step@180@01) N@179@01)))
    (or (= (/ (to_real 1) (to_real 2)) $Perm.No) true))
  
  ))))
 (set-option :rlimit 2895) (check-sat) 
; unsat
(pop) ; 3
; 0.00s
; 
; Check receiver injectivity
(push) ; 3
(assert (not (forall ((j11@285@01 Int) (j12@285@01 Int)) (!
  (implies
    (and
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j11@285@01)
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j11@285@01)
          (< (mod j11@285@01 step@180@01) N@179@01)))
      (and
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j12@285@01)
        (implies
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j12@285@01)
          (< (mod j12@285@01 step@180@01) N@179@01)))
      (=
        ($Seq.index matrix@181@01 j11@285@01)
        ($Seq.index matrix@181@01 j12@285@01)))
    (= j11@285@01 j12@285@01))
  
  :qid |Ref__Integer_value-rcvrInj|))))
 (set-option :rlimit 35449) (check-sat) 
; unsat
(pop) ; 3
; 0.01s
; 
; Definitional axioms for inverse functions
(assert (forall ((j1@285@01 Int)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@285@01)
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) j1@285@01)
        (< (mod j1@285@01 step@180@01) N@179@01)))
    (= (inv@287@01 ($Seq.index matrix@181@01 j1@285@01)) j1@285@01))
  :pattern (($Seq.index matrix@181@01 j1@285@01))
  :qid |Ref__Integer_value-invOfFct|)))
(assert (forall ((r $Ref)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@287@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@287@01 r))
        (< (mod (inv@287@01 r) step@180@01) N@179@01)))
    (= ($Seq.index matrix@181@01 (inv@287@01 r)) r))
  :pattern ((inv@287@01 r))
  :qid |Ref__Integer_value-fctOfInv|)))
; Precomputing data for removing quantified permissions
(define-fun pTaken@288@01 ((r $Ref)) $Perm
  (ite
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@287@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@287@01 r))
        (< (mod (inv@287@01 r) step@180@01) N@179@01)))
    ($Perm.min
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (< (mod (inv@267@01 r) step@180@01) N@179@01)))
        (/ (to_real 1) (to_real 4))
        $Perm.No)
      (/ (to_real 1) (to_real 2)))
    $Perm.No))
(define-fun pTaken@289@01 ((r $Ref)) $Perm
  (ite
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@287@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@287@01 r))
        (< (mod (inv@287@01 r) step@180@01) N@179@01)))
    ($Perm.min
      (-
        (ite
          (and
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@196@01 r))
            (implies
              ($Seq.contains
                ($Seq.range 0 (* M@178@01 step@180@01))
                (inv@196@01 r))
              (< (mod (inv@196@01 r) step@180@01) N@179@01)))
          (/ (to_real 1) (to_real 2))
          $Perm.No)
        (pTaken@252@01 r))
      (- (/ (to_real 1) (to_real 2)) (pTaken@288@01 r)))
    $Perm.No))
(define-fun pTaken@290@01 ((r $Ref)) $Perm
  (ite
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@287@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@287@01 r))
        (< (mod (inv@287@01 r) step@180@01) N@179@01)))
    ($Perm.min
      (ite
        ($Seq.contains ($Seq.range 0 P@182@01) (inv@270@01 r))
        $Perm.Write
        $Perm.No)
      (- (- (/ (to_real 1) (to_real 2)) (pTaken@288@01 r)) (pTaken@289@01 r)))
    $Perm.No))
; Done precomputing, updating quantified chunks
; State saturation: before repetition
;(set-option :timeout 10)
 (set-option :rlimit 94432) (check-sat) 
; unknown
; Chunk depleted?
;(set-option :timeout 500)
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (=
    (-
      (ite
        (and
          ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@267@01 r))
          (implies
            ($Seq.contains
              ($Seq.range 0 (* M@178@01 step@180@01))
              (inv@267@01 r))
            (< (mod (inv@267@01 r) step@180@01) N@179@01)))
        (/ (to_real 1) (to_real 4))
        $Perm.No)
      (pTaken@288@01 r))
    $Perm.No)
  
  ))))
 (set-option :rlimit 2932) (check-sat) 
; unsat
(pop) ; 3
; 0.09s
; 
; Intermediate check if already taken enough permissions
(push) ; 3
(assert (not (forall ((r $Ref)) (!
  (implies
    (and
      ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@287@01 r))
      (implies
        ($Seq.contains ($Seq.range 0 (* M@178@01 step@180@01)) (inv@287@01 r))
        (< (mod (inv@287@01 r) step@180@01) N@179@01)))
    (= (- (/ (to_real 1) (to_real 2)) (pTaken@288@01 r)) $Perm.No))
  
  ))))
 (set-option :rlimit 439610) (check-sat) 
; unknown
(pop) ; 3
; ASSERTION VIOLATION
