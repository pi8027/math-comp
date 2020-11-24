# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `seq.v`
  + lemmas `subset_mapP`, `take_min`, `take_taker`

- in `path.v` 
  + lemmas `prefix_path`, `prefix_sorted`, `infix_sorted`, `suffix_sorted` 

- in `ssralg.v`
  + lemmas `natr1`, `nat1r`

- in `poly.v`
  + definitions `even_poly`, `odd_poly`, `take_poly`, `drop_poly`
  + lemmas `comm_polyD`, `comm_polyM`, `comm_poly_exp`, `root_exp`,
    `root_ZXsubC`, `size_mulXn`, `coef_sumMXn`, `comp_Xn_poly`,
    `coef_comp_poly_Xn`, `comp_poly_Xn`, `size_even_poly`,
    `size_even_poly_eq`, `coef_even_poly`, `even_polyE`, `even_polyD`,
    `even_polyZ`, `even_poly_is_linear`, `even_polyC`,
    `size_odd_poly`, `coef_odd_poly`, `odd_polyE`, `odd_polyC`,
    `odd_polyD`, `odd_polyZ`, `odd_poly_is_linear`, `odd_polyMX`,
    `even_polyMX`, `sum_even_poly`, `sum_odd_poly`, `poly_even_odd`,
    `size_take_poly`, `coef_take_poly`, `take_poly_id`, `take_polyD`,
    `take_polyZ`, `take_poly_is_linear`, `take_poly_sum`,
    `take_poly0l`, `take_poly0r`, `take_polyMXn`, `take_polyMXn_0`,
    `take_polyDMXn`, `size_drop_poly`, `size_drop_poly_eq`,
    `coef_drop_poly`, `drop_poly_eq0`, `sum_drop_poly`, `drop_polyD`,
    `drop_polyZ`, `drop_poly_is_linear`, `drop_poly_sum`,
    `drop_poly0l`, `drop_poly0r`, `drop_polyMXn`, `drop_polyMXn_id`,
    `drop_polyDMXn`, `poly_take_drop`, `eqp_take_drop`
  + canonical instances `even_poly_additive`, `even_poly_linear`,
    `odd_poly_additive`, `odd_poly_linear`, `take_poly_additive`,
    `take_poly_linear`, `drop_poly_additive`, `drop_poly_linear`

- in `polydiv.v`
  + lemmas `Pdiv.RingMonic.drop_poly_rdivp`,
    `Pdiv.RingMonic.take_poly_rmodp`,
    `Pdiv.IdomainMonic.drop_poly_divp`,
    `Pdiv.IdomainMonic.take_poly_modp`

- in `bigop.v`
  + lemmas `big_ord1_eq`, `big_ord1_cond_eq`, `big_nat1_eq`,
    `big_nat1_cond_eq`

- in `eqtype.v`
  + lemmas `existsb` and `exists_inb`

- in `seq.v`
  + lemma `if_nth`

- in `ssrbool.v`
  + lemmas `if_and`, `if_or`, `if_implyb`, `if_impliybC`, `if_add`

- in `ssralg.v`
  + lemma `eqr_sum_div`

- in `ssrnum.v`
  + lemmas `psumr_neq0`, `psumr_neq0P`

- in `ssrnat.v`
  + lemma `leqVgt`
  + lemmas `ltn_half_double`, `leq_half_double`, `gtn_half_double`
  + lemma `double_pred`
  + lemmas `uphalfE`, `ltn_uphalf_double`, `geq_uphalf_double`, `gtn_uphalf_double`
  + lemmas `halfK`, `uphalfK`, `odd_halfK`, `even_halfK`, `odd_uphalfK`, `even_uphalfK`
  + lemmas `leq_sub2rE`, `leq_sub2lE`, `ltn_sub2rE`, `ltn_sub2lE`

- in `ssrint.v`
  + printing only notation for `x = y :> int`, opening `int_scope` on
    `x` and `y` to better match the already existing parsing only
    notation with the introduction of number notations in `ring_scope`

- in `bigop.v`
  + lemmas `big_seq1_id`, `big_nat1_id`, `big_pred1_eq_id`,
    `big_pred1_id`, `big_const_idem`, `big1_idem`, `big_id_idem`,
    `big_rem_AC`, `perm_big_AC`, `big_enum_cond_AC`, `bigD1_AC`,
    `bigD1_seq_AC`, `big_image_cond_AC`, `big_image_AC`,
    `big_image_cond_id_AC`, `Lemma`, `cardD1x`, `reindex_omap_AC`,
    `reindex_onto_AC`, `reindex_AC`, `reindex_inj_AC`, `bigD1_ord_AC`,
    `big_enum_val_cond_AC`, `big_enum_rank_cond_AC`, `big_nat_rev_AC`,
    `big_rev_mkord_AC`, `big_mkcond_idem`, `big_mkcondr_idem`,
    `big_mkcondl_idem`, `big_rmcond_idem`, `big_rmcond_in_idem`,
    `big_cat_idem`, `big_allpairs_dep_idem`, `big_allpairs_idem`,
    `big_cat_nat_idem`, `big_split_idem`, `big_id_idem_AC`,
    `bigID_idem`, `bigU_idem`, `partition_big_idem`,
    `sig_big_dep_idem`, `pair_big_dep_idem`, `pair_big_idem`,
    `pair_bigA_idem`, `exchange_big_dep_idem`, `exchange_big_idem`,
    `exchange_big_dep_nat_idem`, `exchange_big_nat_idem`,
    `big_undup_AC`
- in `matrix.v`
  + definition `Vandrmonde`
  + lemma `det_Vandermonde`

- in `ssralg.v`
  + lemmas `divrN`, `divrNN`
- in `bigop.v`, added lemma `sumnB`.

- in `seq.v`,
  + new higher-order predicate `pairwise r xs` which asserts that the relation
    `r` holds for any i-th and j-th element of `xs` such that i < j.
  + new lemmas `allrel_mask(l|r)`, `allrel_filter(l|r)`, `sub(_in)_allrel`,
    `pairwise_cons`, `pairwise_cat`, `pairwise_rcons`, `pairwise2`,
    `pairwise_mask`, `pairwise_filter`, `pairwiseP`, `pairwise_all2rel`,
    `sub(_in)_pairwise`, `eq(_in)_pairwise`, `pairwise_map`, `subseq_pairwise`,
    `uniq_pairwise`, `pairwise_uniq`, and `pairwise_eq`.
  + new lemmas `zip_map`, `eqseq_all`, and `eq_map_all`.
  + new lemmas `count_undup`, `eq_count_undup`, `rev_take`,
    `rev_drop`, `takeEmask`, `dropEmask`, `filter_iota_ltn`,
    `filter_iota_leq`, `map_nth_iota0` and `map_nth_iota`
  + new lemmas `cat_nilp`, `rev_nilp`, `allrelT`, `allrel_relI`, and
    `pairwise_relI`.

- in `path.v`, new lemmas: `sorted_pairwise(_in)`, `path_pairwise(_in)`,
  `cycle_all2rel(_in)`, `pairwise_sort`, and `sort_pairwise_stable`.
  + new lemmas `cat_sorted2`, `path_le`, `take_path`, `take_sorted`,
    `drop_sorted`, `undup_path`, `undup_sorted`, `count_merge`,
    `eq_count_merge`

- in `path.v`, new lemmas: `pairwise_sorted`, `path_relI`, `cycle_relI`,
  `sorted_relI`, `eq(_in)_sorted`, `mergeA`, `all_merge`, and
  `homo_sort_map(_in)`.

- in `tuple.v`, added Canonical tuple for sort.

- in `interval.v`, new lemmas: `ge_pinfty`, `le_ninfty`, `gt_pinfty`, `lt_ninfty`.
- in `order.v`,
  + the following new structures of ordered types:
    * `(b|t|tb)POrderType`: `porderType` with a top and/or a bottom,
    * `meetSemilatticeType`: meet semilattices,
    * `(b|t|tb)MeetSemilatticeType`:
      `meetSemilatticeType` with a top and/or a bottom,
    * `joinSemilatticeType`: join semilattices,
    * `(b|t|tb)JoinSemilatticeType`:
      `joinSemilatticeType` with a top and/or a bottom,
	* `tLatticeType`: `latticeType` with a top,
	* `tDistrLatticeType`: `distrLatticeType` with a top,
	* `(b|t|tb)OrderType`: `orderType` with a top and/or a bottom,
	* `fin(B|T|TB)POrderType`: `finPOrderType` with a top and/or a bottom,
	* `fin(B)MeetSemilatticeType`:
      finite meet semilattices with/without a bottom,
	* `fin(T)JoinSemilatticeType`:
      finite join semilattices with/without a top, and
	* possibly empty finite lattice structures which involve renamings of
      existing structures (cf Changed and Renamed sections).
  + new factories `meetSemilatticeMixin`, `joinSemilatticeMixin`,
    `totalMeetSemilatticeMixin`, and `totalJoinSemilatticeMixin`.
  + new "big pack" notations `LatticeOfPOrder`, `OrderOfMeetSemilattice`,
    `OrderOfJoinSemilattice`, and `LatticeOfChoiceType`.

- in `order.v`
  + we provide a canonical total order on ordinals and lemmas
    `leEord`, `ltEord`, `botEord`, and `topEord` to translate generic
    symbols to the concrete ones. Because of a shortcoming of the
    current interface, which requires `finOrderType` structures to be
    nonempty, the `finOrderType` is only defined for ordinal which are
    manifestly nonempty (i.e. `'I_n.+1`).
  + new notation `Order.enum A` for `sort <=%O (enum A)`, with new
    lemmas in module `Order`: `cardE`, `mem_enum`, `enum_uniq`,
    `cardT`, `enumT`, `enum0`, `enum1`, `eq_enum`, `eq_cardT`,
    `set_enum`, `enum_set0`, `enum_setT`, `enum_set1`, `enum_ord`,
    `val_enum_ord`, `size_enum_ord`, `nth_enum_ord`, `nth_ord_enum`,
    `index_enum_ord`, `mono_sorted_enum`, and `mono_unique`.
  + a new module `Order.EnumVal` (which can be imported locally), with
    definitions `enum_rank_in`, `enum_rank`, `enum_val` on a finite
    partially ordered type `T`, which are the same as the one from
    `fintype.v`, except they are monotonous when `Order.le T` is
    total. We provide the following lemmas: `enum_valP`,
    `enum_val_nth`, `nth_enum_rank_in`, `nth_enum_rank`,
    `enum_rankK_in`, `enum_rankK`, `enum_valK_in`, `enum_valK`,
    `enum_rank_inj`, `enum_val_inj`, `enum_val_bij_in`,
    `eq_enum_rank_in`, `enum_rank_in_inj`, `enum_rank_bij`,
    `enum_val_bij`, `le_enum_val`, `le_enum_rank_in`, and
    `le_enum_rank`.  They are all accessible via module `Order` if one
    chooses not to import `Order.EnumVal`.
  + a new module `tagnat` which provides a monotonous bijection
    between the finite ordered types `{i : 'I_n & 'I_(p_ i)}`
    (canonically ordered lexicographically), and `'I_(\sum_i p_ i)`,
    via the functions `sig` and `rank`. We provide direct access to
    the components of the former type via the functions `sig1`, `sig2`
    and `Rank`. We provide the following lemmas on these definitions:
    `card`, `sigK`, `sig_inj`, `rankK`, `rank_inj`, `sigE12`,
    `rankE`, `sig2K`, `Rank1K`, `Rank2K`, `rank_bij`, `sig_bij `,
    `rank_bij_on`, `sig_bij_on`, `le_sig`, `le_sig1`, `le_rank`,
    `le_Rank`, `lt_sig`, `lt_rank`, `lt_Rank`, `eq_Rank`, `rankEsum`,
    `RankEsum`, `rect`, and `eqRank`.
  + lemmas `joins_le` and `meets_ge`.
  + new lemmas `le_sorted_ltn_nth`, `le_sorted_leq_nth`,
    `lt_sorted_leq_nth`, `lt_sorted_ltn_nth`, `filter_lt_nth`,
    `count_lt_nth`, `filter_le_nth`, `count_le_nth`,
    `count_lt_le_mem`, `sorted_filter_lt`, `sorted_filter_le`,
    `nth_count_le`, `nth_count_lt`, `count_le_gt`,
    `count_lt_ge`, `sorted_filter_gt`, `sorted_filter_ge`,
    `nth_count_ge`, `nth_count_lt` and `nth_count_eq`

- in `matrix.v`, seven new definitions:
  + `mxblock`, `mxcol`, `mxrow` and `mxdiag` with notations
    `\mxblock_(i < m, j < n) B_ i j`, `\mxcol_(i < m) B_ i`,
    `\mxrow_(j < n) B_ j`, and `\mxdiag_(i < n) B_ i` (and variants
    without explicit `< n`), to form big matrices described by blocks.
  + `submxblock`, `submxcol` and `submxrow` to extract blocks from the
    former constructions. There is no analogous for `mxdiag` because
    one can simply apply `submxblock A i i`.
  + We provide the following lemmas on these definitions:
    `mxblockEh`, `mxblockEv`, `submxblockEh`, `submxblockEv`,
    `mxblockK`, `mxrowK`, `mxcolK`, `submxrow_matrix`,
    `submxcol_matrix`, `submxblockK`, `submxrowK`, `submxcolK`,
    `mxblockP`, `mxrowP`, `mxcolP`, `eq_mxblockP`, `eq_mxblock`,
    `eq_mxrowP`, `eq_mxrow`, `eq_mxcolP`, `eq_mxcol`, `row_mxrow`,
    `col_mxrow`, `row_mxcol`, `col_mxcol`, `row_mxblock`,
    `col_mxblock`, `tr_mxblock`, `tr_mxrow`, `tr_mxcol`,
    `tr_submxblock`, `tr_submxrow`, `tr_submxcol`, `mxsize_recl`,
    `mxrow_recl`, `mxcol_recu`, `mxblock_recl`, `mxblock_recu`,
    `mxblock_recul`, `mxrowEblock`, `mxcolEblock`, `mxEmxrow`,
    `mxEmxcol`, `mxEmxblock`, `mxrowD`, `mxrowN`, `mxrowB`, `mxrow0`,
    `mxrow_const`, `mxrow_sum`, `submxrowD`, `submxrowN`, `submxrowB`,
    `submxrow0`, `submxrow_sum`, `mul_mxrow`, `mul_submxrow`,
    `mxcolD`, `mxcolN`, `mxcolB`, `mxcol0`, `mxcol_const`,
    `mxcol_sum`, `submxcolD`, `submxcolN`, `submxcolB`, `submxcol0`,
    `submxcol_sum`, `mxcol_mul`, `submxcol_mul`, `mxblockD`,
    `mxblockN`, `mxblockB`, `mxblock0`, `mxblock_const`,
    `mxblock_sum`, `submxblockD`, `submxblockN`, `submxblockB`,
    `submxblock0`, `submxblock_sum`, `mul_mxrow_mxcol`,
    `mul_mxcol_mxrow`, `mul_mxrow_mxblock`, `mul_mxblock_mxrow`,
    `mul_mxblock`, `is_trig_mxblockP`, `is_trig_mxblock`,
    `is_diag_mxblockP`, `is_diag_mxblock`, `submxblock_diag`,
    `eq_mxdiagP`, `eq_mxdiag`, `mxdiagD`, `mxdiagN`, `mxdiagB`,
    `mxdiag0`, `mxdiag_sum`, `tr_mxdiag`, `row_mxdiag`, `col_mxdiag`,
    `mxdiag_recl`, `mxtrace_mxblock`, `mxdiagZ`, `diag_mxrow`,
    `mxtrace_mxdiag`, `mul_mxdiag_mxcol`, `mul_mxrow_mxdiag`,
    `mul_mxblock_mxdiag`, and `mul_mxdiag_mxblock`.
   + adding missing lemmas `trmx_conform` and `eq_castmx`.

- in `mxalgegra.v`,
  + Lemmas about rank of block matrices with `0`s inside
    `rank_col_mx0`, `rank_col_0mx`, `rank_row_mx0`, `rank_row_0mx`,
    `rank_diag_block_mx`, and `rank_mxdiag`.
  + we provide an equality of spaces `eqmx_col` between `\mxcol_i V_
    i` and the sum of spaces `\sum_i <<V_ i>>)%MS`.

- in `bigop.v`:
  + Lemmas `big_nat_widenl`, `big_geq_mkord`
- in `ssrint.v`,
  + Lemmas: `mulr_absz`, `natr_absz`, `lez_abs`

- In `ssralg.v`
  + new lemma `fmorph_eq`

- In `rat.v`
  + new lemmas `minr_rat`, `maxr_rat`

- In `intdiv.v`
  + new definition `lcmz`
  + new lemmas `dvdz_lcmr`, `dvdz_lcml`, `dvdz_lcm`, `lcmzC`, `lcm0z`,
    `lcmz0`, `lcmz_ge0`, `lcmz_neq0`
  + new lemma `lez_pdiv2r`

- In `ssrnum.v`:
  + new lemma `eqNr`

### Changed

- in `poly.v`:
  + generalize `eq_poly`

- in `poly.v`:
  + made hornerE preserve powers

### Renamed

- across the library, the deprecation mechanism to use has been changed from the
  `deprecate` notation to the `deprecated` attribute (cf. Removed section).
- in `order.v`,
  + For an ordered type instance `T`, the class record of `T^d^d` is now
    convertible with that of `T` except for complemented lattice structures.
    To make duals definitionally involutive as such, the mixins of `porderType`
    and `distrLatticeType` (whose duals are themselves) are redefined to include
    some dual axioms (e.g., antisymmetry of `<=^d`), and the mixins of
    `tPOrderType` and `joinSemilatticeType` (whose duals are `bPOrderType` and
    `meetSemilatticeType` respectively) are defined as duals of the mixins of
    the dual structures. Provided factories hide these internal details of
    mixins. Caveat: duals of structures are not definitionally involutive yet,
    since structure records cannot be primitive for technical reasons and
    `dual_display` is opaque.
  + The `latticeType` structure has been redefined as the join of
    `meetSemilatticeType` and `joinSemilatticeType` that have no extra mixin.
    To declare a canonical `latticeType` instance of type `T`, one has to
    declare canonical semilattice type instances of `T` first, and then use
    `[latticeType of T]` to compute their join.
  + The `meetJoinMixin` factory has been redefined not to require the
    distributivity. One that requires distributivity has been renamed to
    `distrMeetJoinMixin` (cf Renamed section).
  + The finite lattice structures `finLatticeType`, `finDistrLatticeType`, and
    `finOrderType` (excluding `finCDistrLatticeType`) are now allowed to be
    empty. The original (nonempty) finite lattice structures (including
    `finCDistrLatticeType`) are renamed to have prefix `TB` (cf Added and
    Renamed sections).

### Renamed

- in `path.v`,
  + `sub_(path|cycle|sorted)_in` -> `sub_in_(path|cycle|sorted)`
  + `eq_(path|cycle)_in` -> `eq_in_(path|cycle)`

- in `order.v`
  + `join_(|sup_|min_)seq` -> `joins_(|sup_|min_)seq`
  + `meet_(|sup_|min_)seq` -> `meets_(|sup_|min_)seq`
  + `join_(sup|min)` -> `joins_(sup|min)`
- in `order.v`,
  + the following structures have been renamed (cf Added and Changed sections):
    * `finLatticeType` -> `finTBLatticeType`
    * `finDistrLatticeType` -> `finTBDistrLatticeType`
    * `finCDistrLatticeType` -> `finCTBDistrLatticeType`
    * `finOrderType` -> `finTBOrderType`
  + the following factories have been renamed (cf Changed section):
    * `latticeMixin` -> `latticePOrderMixin`
    * `meetJoinMixin` -> `distrMeetJoinMixin`

### Removed

### Infrastructure

### Misc

