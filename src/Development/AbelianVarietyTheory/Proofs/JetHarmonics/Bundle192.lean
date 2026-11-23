module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle042
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle099
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle085
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle102
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle080
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle084
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle079
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle176
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle179
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle122
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle132
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle120
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle191
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle060
public import Formalism.LocalRingCardinality.Bundle002
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.LargePkg

theorem not_inPsi_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    {τ : E →+* ℂ} (h : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h'
  unfold InPsi at h h'
  rw [ComplexEmbedding.conjugate_coe_eq, h] at h'
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h'
  have e := H.sqrt_neg_disc_sq
  rw [hr] at e
  have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e
  have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem pkg_of_supply (P : RF.Par) (l : ℕ) {C : Type} [Field C] (V : VF C) (hV : V.l = l) (Z : Finset P.Pl)
    (hZ : RF.IsReps P Z) (hw : ∀ z, 0 ≤ P.w z) (big : P.Pl → Fin 2 → ZMod P.d → Prop)
    (rk : P.Pl → Fin 2 → ZMod P.d → ℕ) (b : P.Pl → Fin 2 → ZMod P.d → ℕ → ℕ) (K s nW : ℕ) (ν : ℝ)
    (hK : ∀ z g a, rk z g a ≤ K) (hb : ∀ z g a i j, i ≤ j → j < rk z g a → b z g a j ≤ b z g a i)
    (h0 : ∀ z g a, 0 < rk z g a → b z g a 0 ≤ s * (l - 1)) (hrows : 2 * K * s * Z.card ≤ nW)
    (hS : Supply V P.d P.Pl Z (P.k - 1) P.m big rk (fun z g a => gap (rk z g a) (b z g a)) nW ν) :
    ∃ Pk : RF.PkgZero P l, Pk.ν = ν := by
  obtain ⟨I, J, fI, fJ, X, F, hn, hrk, hval⟩ := hS
  refine ⟨{ R := { C := C, V := V, hVl := hV, I := I, J := J, X := X, F := F, hn := hn }
            Z := Z, hZ := hZ, ga := fun z g a => gap (rk z g a) (b z g a), K := K, s := s, nW := nW, T := 1, ν := ν
            T_one := le_rfl, w_nonneg := hw, supp := ?_, first := ?_, what₂ := hrows, val := hval }, rfl⟩
  · intro z hz g a k hk
    obtain ⟨h1, h2⟩ := (GlobalTheory.RowAt.gap_sums (rk z g a) (b z g a) (hb z g a)).1 k hk
    exact ⟨h1, h2.trans_eq (hrk z hz g a).2.symm, h2.trans (hK z g a)⟩
  · intro z _ g a
    obtain ⟨h1, h2⟩ := GlobalTheory.RowAt.gap_sums (rk z g a) (b z g a) (hb z g a)
    rcases Nat.eq_zero_or_pos (rk z g a) with h | h
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun k _ => ?_) (Nat.zero_le _)
      by_contra hk
      have := h1 k hk
      omega
    · exact le_of_eq_of_le ((h2 K (hK z g a)).1 0 h) (h0 z g a h)

theorem pkg_of_labels (hU : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {lv : Level H}
    {Xo : Moduli Dw lv} {c : Coeff lv} [StarRing (𝓞 E)] (hstar : ∀ x : 𝓞 E, star x = H.bar x)
    (N : NumDatum) (j : ℕ) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ N.R.m)
    (hpsi : ∀ z, InPsi H (pl z)) (hp : Dw.p = (N.R.sigW j).1) (hq : Dw.q = (N.R.sigW j).2) (ha : DomW Dw a)
    {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (hy : y.IsAlg) (C3 : IntChart T io y)
    {C : Type} [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C) (hι : EmbOK T V ι) {k : ℕ}
    (Y : FBChart C V (𝓞 E) (chD C3.ch)) (hY : IsBC C3 ι k Y) (hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E)
    (nW : ℕ) (ν : ℝ) (hν : (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW)
    (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) (sel : ZMod d → Fin 2)
    (hsel : (Even d ∧ ∀ s : ZMod d, (0 = sel s ↔ Even s.val)) ∨ ∀ s, 0 = sel s)
    (tau : RPl N.R → Fin 2 → ZMod d → (E →+* ℂ))
    (htau : ∀ z g s, tau z g s = if g = sel s then pl (pos z s.val) else ComplexEmbedding.conjugate (pl (pos z s.val)))
    (Z : Finset (RPl N.R)) (hZ : RF.IsReps (parAt N j d pos) Z) (hne : Z.Nonempty)
    (hbij : Function.Bijective fun x : Z × Fin 2 × ZMod d => tau x.1.1 x.2.1 x.2.2)
    (hfrob : ∀ z g, FrobOrd V io ι (tau z g)) (hw : ∀ z, 0 ≤ N.w j z) (s : ℕ)
    (hs : ∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (V.l - 1)) (hrows : 2 * N.R.r * s * N.R.f ≤ nW) :
    ∃ Pk : RF.PkgZero (parAt N j d pos) V.l, Pk.ν = ν := by
  have hk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  let lab : Lab E Z d := ⟨fun o => tau o.1, N.R.k - 1, j, N.R.m - j, fun _ g s => g = sel s⟩
  have hconj : ∀ z s, tau z 1 s = ComplexEmbedding.conjugate (tau z 0 s) := by
    intro z s
    rw [htau, htau]
    generalize sel s = g
    fin_cases g
    · simp
    · have : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => by
        ext x; simp
      simp [this]
  have hA : LabArith V io ι lab :=
    { inj := hbij.1
      conj := fun o s => hconj o.1 s
      frob := fun o g s x => hfrob o.1 g s x
      sep := fun x x' hx => (GlobalTheory.T.cmEmbeddings_integral_and_distinct_mod_maximal E H lv c T io C V ι hι hunr).2 _ _ fun h => hx (hbij.1 h)
      unr := fun o g => GlobalTheory.T.exists_idempotent_frobeniusOrbit_unramified E H lv c T io C V ι hι hunr d (tau o.1 g) (hfrob o.1 g) }
  have hR : lab.RankOK Dw := by
    intro o
    refine ⟨fun g s => ?_, fun g s h => ?_, fun g s h => ?_⟩
    · change 1 - g = sel s ↔ ¬ g = sel s
      generalize sel s = g'
      revert g g'
      decide
    · change Dw.mult (tau o.1 g s) = N.R.k - 1 + j
      rw [htau, if_pos (show g = sel s from h), Datum.mult]
      exact (if_pos (hpsi _)).trans (by omega)
    · change Dw.mult (tau o.1 g s) = N.R.m - j
      rw [htau, if_neg (show ¬ g = sel s from h), Datum.mult]
      exact (if_neg (not_inPsi_conj H (hpsi _))).trans hq'
  have h1 := GlobalTheory.T.rowData_supplied_at_pairs_of_places hU E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hunr Z d lab hA hbij.2 hR
    (show N.R.m - j < N.R.k - 1 by omega) (fun _ => hsel) a ha nW ν hν
  have hm : lab.j + lab.j' = N.R.m := show j + (N.R.m - j) = N.R.m by omega
  rw [hm] at h1
  have h2 := GlobalTheory.RowAt.supply_extend C V d (RPl N.R) Z (N.R.k - 1) N.R.m (fun _ g s => g = sel s)
    (fun z g s => Dw.mult (tau z g s)) (fun z g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) nW ν hne h1
  have hcard : Z.card ≤ N.R.f := by
    refine (Finset.card_le_univ Z).trans_eq ?_
    simp [Ranks.f_eq_ord, Formalism.HC.Frame.card_A]
  refine pkg_of_supply (parAt N j d pos) V.l V rfl Z hZ hw (fun _ g s => g = sel s)
    (fun z g s => Dw.mult (tau z g s)) (fun z g s i => a (tau z g s, i)) N.R.r s nW ν ?_ ?_ ?_ ?_ h2
  · intro z g s
    unfold Datum.mult Ranks.r
    split_ifs <;> omega
  · intro z g s i i' h h'
    exact ha (tau z g s) ⟨i, h.trans_lt h'⟩ ⟨i', h'⟩ h
  · intro z g s h
    exact hs _ h
  · exact (Nat.mul_le_mul_left _ hcard).trans hrows

theorem pkgZero : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgZeroSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _ hstar N j pl a hj1 hjm hT hp hq ha la h2 hlq hld hM _ T io e hO y hy C3 nW ν hν
    hphi hw s hs hrows
  obtain ⟨C, _, _, V, ι, hV, hι, hac, hcpl, hla, hunit, hnu⟩ := GlobalTheory.T.exists_closedComplete_field_over_place E H Dw lv Xo c la T io e hO
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl (hV ▸ ne_two_of_not_small h2)
    (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M (hunit _ hM)
  have hν' := hnu y C3 lv.M a nW ν hν
  rw [← hV] at h2 hlq hld hphi hs ⊢
  have hunr := hT.unr V.l V.l_prime h2 hlq hld
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hT.psi _).2 ⟨z, rfl⟩
  by_cases hin : Inert N V.l
  · obtain ⟨Z, hZ, hne, hev, hbij, hfr⟩ := GlobalTheory.T.realPlaceLabelling_inert_frobenius_not_conj E H lv c N pl hT la T io C V ι hι hV hla hin hphi j
    refine ⟨N.ordP V.l, inferInstance, N.pos V.l, pkg_of_labels hU hstar N j pl a hj1 hjm hpsi hp hq ha hy C3 V ι hι Y hY
      hunr nW ν hν' (N.ordP V.l) (N.pos V.l) RF.bg (Or.inl ⟨hev, fun s => ?_⟩) (tauIn N pl V.l) (fun _ _ _ => rfl)
      Z hZ hne hbij (fun z g => (hfr z g).1) hw s hs hrows⟩
    unfold RF.bg
    split_ifs with h <;> simp [h]
  · have hsp : N.cls V.l = PrimeClass.splitK := by
      unfold Inert NumDatum.cls primeClass at *
      rw [if_neg h2, if_neg hlq, if_neg hld] at hin ⊢
      split_ifs at hin ⊢ <;> simp_all
    obtain ⟨d, _, pos, Z, hZ, hne, hbij, hfr⟩ := GlobalTheory.T.cmType_frobenius_orbits_label_at_split_prime E H lv c N pl hT la T io C V ι hι hV hla hsp j
    exact ⟨d, inferInstance, pos, pkg_of_labels hU hstar N j pl a hj1 hjm hpsi hp hq ha hy C3 V ι hι Y hY
      hunr nW ν hν' d pos (fun _ => 0) (Or.inr fun _ => rfl) (tauSp N pl pos) (fun _ _ _ => rfl)
      Z hZ hne hbij hfr hw s hs hrows⟩

end GlobalTheory.LargePkg
end

section

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.PkgConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

noncomputable def gaC (N : NumDatum) (Dw : Datum H) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ)
    (z : RPl N.R) (s : ZMod 2) : ℕ → ℕ :=
  gap (Dw.mult (tauC N pl z s)) fun i => a (tauC N pl z s, i)

theorem exists_rowFam (hUp : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p)
    {Dw : Datum H} {lv : Level H} (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] :
    AllPts Xo c fun N j l pl a nW ν => PhiC N l →
      Function.Bijective (fun x : RPl N.R × ZMod 2 => tauC N pl x.1 x.2) ∧
      ∃ R : RF.RowFam (parOf N j l) l 2, (∀ z, (R.X z).Alt) ∧
        (∀ z s, (R.X z).rkF 0 s = Dw.mult (tauC N pl z s)) ∧
        @RF.ValBlocksC R.C R.fC R.V (parOf N j l).Pl _ R.I R.J R.fI R.fJ R.X R.F nW (gaC N Dw pl a) ν := by
  intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 _ _ hM _ T io e hover y hy C3 nW ν hν hC
  obtain ⟨C, _, _, V, ι, hVl, hι, hac, hcpl, hla, hunit, hconv⟩ :=
    GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hover
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl
    (hVl ▸ (fun h => h2 (h ▸ N.H.two_mem_small) : resCharOf la ≠ 2)) (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M (hunit _ hM)
  obtain ⟨hA, hS⟩ := GlobalTheory.LabSelf.arithS_tauC E H lv c N pl hP la T io C V ι hι hVl hla (hVl ▸ hC)
    (N.R.k - 1) j (N.R.m - j)
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
  have hrk : (⟨tauC N pl, N.R.k - 1, j, N.R.m - j⟩ : LabS E (RPl N.R)).RankOK Dw := by
    intro z
    have h10 : ¬ (1 : ZMod 2) = 0 := by decide
    have t0 : tauC N pl z 0 = pl z := if_pos rfl
    have t1 : tauC N pl z 1 = ComplexEmbedding.conjugate (pl z) := if_neg h10
    have m0 : Dw.mult (pl z) = Dw.p := if_pos (hpsi z)
    have m1 : Dw.mult (ComplexEmbedding.conjugate (pl z)) = Dw.q :=
      if_neg (GlobalTheory.LabSelf.not_inPsi_conj H (hpsi z))
    refine ⟨?_, ?_⟩
    · show Dw.mult (tauC N pl z 0) = N.R.k - 1 + j
      rw [t0, m0]; omega
    · show Dw.mult (tauC N pl z 1) = N.R.m - j
      rw [t1, m1, hq']
  obtain ⟨I, J, fI, fJ, X, F, hX, hval⟩ := GlobalTheory.T.rowData_supplied_at_selfConjugate_places hUp E H Dw lv Xo c hstar T io y C3 C V ι hι lv.M Y hY hy
    (RPl N.R) ⟨tauC N pl, N.R.k - 1, j, N.R.m - j⟩ hA hS hrk (by show N.R.m - j < N.R.k - 1; omega) a hdom nW ν
    (hconv y C3 lv.M a nW ν hν)
  refine ⟨⟨hA.inj, hS⟩, { C := C, V := V, hVl := hVl, I := I, J := J, fI := fI, fJ := fJ, X := X, F := F, hn := ?_ },
    fun z => (hX z).2.2.1, fun z => (hX z).2.2.2, hval⟩
  intro z
  refine ⟨(hX z).1, (hX z).2.1.trans ?_⟩
  show j + (N.R.m - j) = N.R.m
  omega

private theorem rest_add (n K : ℕ) (h1 : 1 ≤ n) (hK : n ≤ K) (ga : ZMod 2 → ℕ → ℕ) :
    ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 K, (if s = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga s k) =
      ∑ s : ZMod 2, ((∑ k ∈ Finset.Icc 1 K, k * ga s k : ℕ) : ℝ) - (n : ℝ) * ga 0 n := by
  have e : (n : ℝ) * ga 0 n =
      ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 K, if s = 0 ∧ k = n then (k : ℝ) * ga s k else 0 := by
    rw [Finset.sum_eq_single 0, Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨h1, hK⟩) h
    · intro b _ hb; simp [hb]
    · simp
  rw [e, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem packages_conj : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgPhiCSt Xo c ∧ PkgZeroCSt Xo c := by
  intro hUp E _ _ _ H Dw lv Xo c _
  refine ⟨?_, ?_⟩
  · intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin T io e hover y hy C3 nW ν hν hC T0 θ0 C1 hdeg hrows
    obtain ⟨hbij, R, halt, hrk, hval⟩ := exists_rowFam hUp Xo c hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin
      T io e hover y hy C3 nW ν hν hC
    have hmk := N.R.m_add_three_le_k
    have hp' : Dw.p = N.R.k + j - 1 := hp
    have hq' : Dw.q = N.R.m - j := hq
    have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
    have hpsi : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
    have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
      unfold Datum.mult; split_ifs <;> omega
    have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i))
      (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
    have hmain : ∀ z, gaC N Dw pl a z 0 (N.R.k - 1) = gapW N pl a z := by
      intro z
      have t0 : tauC N pl z 0 = pl z := if_pos rfl
      have hm : Dw.mult (pl z) = Dw.p := if_pos (hpsi _)
      unfold gaC
      rw [t0, hm]
      unfold gap gapW
      rw [if_pos (by omega), if_pos (by omega)]
      rfl
    have hDF : DF Dw a = ∑ z, ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 N.R.r, k * gaC N Dw pl a z s k := by
      unfold DF
      rw [← hbij.sum_comp (fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)), Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun s _ => ((hgs _).2 _ (hmul _)).2.symm
    refine ⟨{ R := R, alt := halt, gaC := gaC N Dw pl a, W := gapW N pl a, nW := nW, T := T0, θ0 := θ0,
              rest := restOf N Dw pl a, ν := ν, supp := ?_, main := hmain, rest_eq := ?_, what₂ := hrows,
              deg := hdeg, val := hval }, rfl, rfl⟩
    · intro z s k hk
      rw [hrk]
      exact (hgs _).1 k hk
    · show restOf N Dw pl a = ∑ z : RPl N.R, ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 N.R.r,
        (if s = 0 ∧ k = N.R.k - 1 then (0 : ℝ) else (k : ℝ) * gaC N Dw pl a z s k)
      simp only [rest_add (N.R.k - 1) N.R.r (by omega) (by omega), hmain]
      unfold restOf
      rw [hDF, Finset.sum_sub_distrib, ← Finset.mul_sum]
      push_cast [Nat.cast_sub (show 1 ≤ N.R.k by omega)]
      rfl
  · intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin T io e hover y hy C3 nW ν hν hC hw s hfirst hrows
    obtain ⟨-, R, -, hrk, hval⟩ := exists_rowFam hUp Xo c hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin
      T io e hover y hy C3 nW ν hν hC
    have hmk := N.R.m_add_three_le_k
    have hp' : Dw.p = N.R.k + j - 1 := hp
    have hq' : Dw.q = N.R.m - j := hq
    have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
    have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
      unfold Datum.mult; split_ifs <;> omega
    have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i))
      (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
    have hcard : Fintype.card (RPl N.R) = N.R.f := by
      simp [RPl, Ranks.f, Ranks.n, ZMod.card, N.R.card_A]
    refine ⟨{ R := R, gaC := gaC N Dw pl a, K := N.R.r, s := s, nW := nW, T := 1, ν := ν, T_one := le_rfl,
              w_nonneg := hw, supp := ?_, first := ?_, what₂ := ?_, val := hval }, rfl⟩
    · intro z σ k hk
      rw [hrk]
      have h := (hgs _).1 k hk
      exact ⟨h.1, h.2, h.2.trans (hmul _)⟩
    · intro z σ
      rcases Nat.eq_zero_or_pos (Dw.mult (tauC N pl z σ)) with h0 | h0
      · refine le_trans (le_of_eq (Finset.sum_eq_zero fun k _ => ?_)) (Nat.zero_le _)
        by_contra hk
        have h := (hgs _).1 k hk
        omega
      · exact le_trans (le_of_eq (((hgs _).2 _ (hmul _)).1 0 h0)) (hfirst _ h0)
    · show 4 * N.R.r * s * Fintype.card (RPl N.R) ≤ nW
      rw [hcard]; exact hrows

end GlobalTheory.PkgConj
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
namespace GlobalTheory.RecDepth

theorem depth_le : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  intro hHT D T h j hj hinj EX w c hO hR la y
  by_cases hla : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal
  · obtain ⟨i, hi⟩ := hla
    exact GlobalTheory.T.thetaLatticeDepth_le_at_places_over_level hHT D T h j hj hinj EX w c hO hR la i hi y
  · exact GlobalTheory.T.thetaLatticeDepth_le_at_places_prime_to_level D T h j hj hinj EX w c hO hR la (fun i hi => hla ⟨i, hi⟩) y

end GlobalTheory.RecDepth
end

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem leaves_sup_span_lemmaS_of_formTieK : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc), (∀ (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J), ∃ (T : Full D) (h : LawsP T.toTop) (j : ℕ) (hj : InR D j) (p : ℕ) (_ : Algebra (recB h.toLawsCore).KO K), ∃ z act, ∃ ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), FormTieK (recPJ h j hj) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO O v i z act ∧ IsLevAct T.toTop h j (kaR Tp hK j) ℓ act ∧ LawsFull T ∧ (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) ∧ OneCover T.toTop j ∧ 0 < p ∧ Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h.toLawsCore) j (kaR Tp hK j) ∧ ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) (kaR Tp hK j) ∧ WeightAlgebra.H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j)) → LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O := by
  intro hCI D L Pm Tp hK hinj EX K _ _ _ Bs Df S P _ _ oc O H
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J),
      (IsLatIn ⊤ (O.Ms i) ∧ ∀ g : P, (O.Ms i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Ms i) ∧
      (IsLatIn ⊤ (O.Th v i) ∧ IsLatIn ⊤ (O.ThK v i)) ∧
      (O.Th v i ≤ O.Ms i ∧ (∀ g : P, (O.Th v i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Th v i) ∧
        O.σ v i ≠ 0 ∧ O.Th v i ≤ Formalism.EigenvalueLevelCeiling.sc (O.σ v i) (O.ThK v i)) := by
    intro v i
    obtain ⟨T, h, j, hj, p, inst, z, act, ℓ, hFK, hA, hFull, hxi, hO, hp, hLat, hSp, hH⟩ := H v i
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.RunDepth.run_weights_sum D L Pm Tp hK j hj
    have hF := hFK.toFormTie (shortTh_fg _ hinj EX hp _ _ _ _ hLat.toIsLattice hH)
      (productsShort_rec hCI D T.toTop h j hj hFull.sh hO (hFull.lvA j hj 0) _ _ _ _ h1 h2 h3 h4 (kaWt_n _ _ _ _))
    exact ⟨supLattice_isLatIn_stable D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF hLat
        (levAct_mem_Mlat D T.toTop h j hj _ P ℓ act hA),
      theta_spans_isLatIn D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF hp h1 h2 h3 hLat.toIsLattice hSp hH,
      GlobalTheory.scaledSpan_clauses D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF h1 h2 h3 hH
        (levAct_theta hCI D T h j hj hFull hxi _ _ _ _ _ h1 h2 h3 h4 P ℓ act hA)⟩
  obtain ⟨v₀, -⟩ := exists_place3 K
  exact ⟨fun i => (key v₀ i).1,
    fun w _ => ⟨fun i => (key w i).2.1, fun i => (key (conjPl w) i).2.1⟩,
    fun w _ => ⟨fun i => (key w i).2.2, fun i => (key (conjPl w) i).2.2⟩⟩

end GlobalTheory.FormTies
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unscaledDepth_le_placeOverTwo : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitAt H.d p → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la = p → ∀ (k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuW Xo c la k a n ≤ (((ramOverZ la : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  first | exact @GlobalTheory.CharDepth.nuW_le_two | exact GlobalTheory.CharDepth.nuW_le_two | (intros; apply GlobalTheory.CharDepth.nuW_le_two <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZeroForm_cutoff_tendsto_of_density_domination : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (Y : Finset ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → (∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ((∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)‖ ≤ h c)) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re) (𝓝[>] 0) (𝓝 (p.RR f 0 w [] []).re) := by
  first | exact @GlobalTheory.levelZeroForm_cutoff_tendsto_of_domination | exact GlobalTheory.levelZeroForm_cutoff_tendsto_of_domination | (intros; apply GlobalTheory.levelZeroForm_cutoff_tendsto_of_domination <;> assumption)
end
