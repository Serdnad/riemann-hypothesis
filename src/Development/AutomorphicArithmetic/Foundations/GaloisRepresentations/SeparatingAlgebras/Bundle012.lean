module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle144
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle213
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle215
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle225
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle010
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle061
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem eq_one_of_fin_inf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {x : UA E a}
    (hf : x ∈ finU (E := E) (n := a)) (hi : x ∈ infU E a) : x = 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) x.1 = 1 := hf
  have h2 : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hi
  exact Subtype.ext (ga_ext (by rw [h1]; simp) (by rw [h2]; simp))

private theorem cLoc_of_inf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
    (w : HeightOneSpectrum (𝓞 E)) {x : UA E a} (hx : x ∈ infU E a) : cLoc w x = 1 := by
  have h2 : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  have e : cLoc w x = Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by
    ext i j
    rfl
  rw [e, h2, map_one]

private theorem conj_form {G : Type} [Group G] {s j g g' γ x c : G} (hj : j * g' = g' * j) (hj2 : j * g = g * j)
    (hxg : g * x = x * g) (hxj : j * x = x * j) (h : s * j * g' = γ * (s * j * g) * x * c) :
    γ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ := by
  have h0 : γ * (s * j * g) = s * j * g' * c⁻¹ * x⁻¹ := by
    rw [h]; group
  have h1 : γ = s * j * g' * c⁻¹ * x⁻¹ * (s * j * g)⁻¹ := eq_mul_inv_of_mul_eq h0
  have hc : Commute x (g⁻¹ * j⁻¹) :=
    (Commute.inv_right (show Commute x g from hxg.symm)).mul_right (Commute.inv_right (show Commute x j from hxj.symm))
  have hq : x⁻¹ * (g⁻¹ * j⁻¹) = g⁻¹ * j⁻¹ * x⁻¹ := (hc.inv_left).eq
  have hq2 : g⁻¹ * j⁻¹ = j⁻¹ * g⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hj2]
  calc γ = s * (j * g') * c⁻¹ * (x⁻¹ * (g⁻¹ * j⁻¹)) * s⁻¹ := by rw [h1]; group
    _ = s * (g' * j) * c⁻¹ * (j⁻¹ * g⁻¹ * x⁻¹) * s⁻¹ := by rw [hj, hq, hq2]
    _ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ := by group

theorem UpperTheory.Gal.Gen.sep_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.LocComm → UpperTheory.Gal.Gen.RatFin → UpperTheory.Gal.Gen.Sep := by
  intro hLev hComm hRat E _ _ _ a w₀ hs K hK J hJ S T hT hinj
  classical
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E a
  have hI : IsCompact (infU E a : Set (UA E a)) := isCompact_iff_compactSpace.2 inferInstance
  obtain ⟨hL0, hmem0, -, -, -, -⟩ := hLev E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have hC0 : IsCompact (lev K w₀ (J 0) : Set (UA E a)) := hL0.compact

  let P : UA E a × UA E a × UA E a × UA E a × UA E a → UA E a :=
    fun q => q.1 * q.2.2.1 * q.2.2.2.1 * q.2.1⁻¹ * q.2.2.2.2 * q.1⁻¹
  let D : Set (UA E a × UA E a × UA E a × UA E a × UA E a) :=
    (S : Set (UA E a)) ×ˢ (T : Set (UA E a)) ×ˢ (T : Set (UA E a)) ×ˢ
      (lev K w₀ (J 0) : Set (UA E a)) ×ˢ (infU E a : Set (UA E a))
  have hD : IsCompact D :=
    S.finite_toSet.isCompact.prod (T.finite_toSet.isCompact.prod (T.finite_toSet.isCompact.prod (hC0.prod hI)))
  have hP : Continuous P := by
    simp only [P]
    fun_prop
  have hR : (P '' D ∩ (ratU E a : Set (UA E a))).Finite := (hRat E a).1 _ (hD.image hP)

  let Y : UA E a × UA E a → GL (Fin a) (w₀.adicCompletion E) := fun q => cLoc w₀ (q.1⁻¹ * q.2 * q.1)
  let F : Set (GL (Fin a) (w₀.adicCompletion E)) :=
    Y '' ((S : Set (UA E a)) ×ˢ ((P '' D ∩ (ratU E a : Set (UA E a))) \ {1}))
  have hF : F.Finite := (S.finite_toSet.prod (hR.subset Set.diff_subset)).image _
  have hne : ∀ y ∈ F, y ≠ 1 := by
    rintro _ ⟨⟨s, γ⟩, ⟨-, ⟨-, hγ⟩, hγ1⟩, rfl⟩ e
    refine hγ1 ((hRat E a).2 w₀ γ hγ ?_)
    simp only [Y, map_mul, map_inv] at e
    have := congrArg (fun t => cLoc w₀ s * t * (cLoc w₀ s)⁻¹) e
    simpa [mul_assoc] using this
  have ev : ∀ y ∈ F, ∀ᶠ n in Filter.atTop, y ∉ J n := by
    intro y hy
    obtain ⟨n, hn⟩ := hJ.small {y}ᶜ (isOpen_compl_singleton.mem_nhds (by simpa using (hne y hy).symm))
    filter_upwards [Filter.eventually_ge_atTop n] with m hm hym
    exact hn (hJ.anti hm hym) rfl
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 ((Set.Finite.eventually_all hF).2 ev)
  refine ⟨n₀, fun n hn y g hg g' hg' γ hγ x hx c hc h => ?_⟩
  obtain ⟨⟨s, hsS⟩, ⟨j, hjL, hjJ⟩⟩ := y
  simp only at h
  obtain ⟨hLn, -, hcl, hck, -, hmono⟩ := hLev E a w₀ hs K hK (J n) (hJ.isOpen n) (hJ.compact n)
  have hcJ : cLoc w₀ c ∈ J n := hcl c hc
  have hcC0 : c ∈ lev K w₀ (J 0) := hmono (J 0) c hc (hJ.anti (Nat.zero_le n) hcJ)
  have hjC0 : j ∈ lev K w₀ (J 0) := (hmem0 j).2 ⟨1, K.one_mem, j, hjL, hjJ, (one_mul j).symm⟩
  have hgF : g ∈ finU (E := E) (n := a) := (hT g hg).1
  have hgF' : g' ∈ finU (E := E) (n := a) := (hT g' hg').1
  have hcF : c ∈ finU (E := E) (n := a) := hLn.fin hc
  have hjF : j ∈ finU (E := E) (n := a) := (Subgroup.mem_inf.1 hjL).1
  have hg1 : cLoc w₀ g = 1 := (hT g hg).2 w₀ (not_apart_self w₀)
  have hg1' : cLoc w₀ g' = 1 := (hT g' hg').2 w₀ (not_apart_self w₀)
  have hx1 : cLoc w₀ x = 1 := cLoc_of_inf w₀ hx
  have hγeq : γ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ :=
    conj_form (hComm E a w₀ j g' hjL (hT g' hg').2) (hComm E a w₀ j g hjL (hT g hg).2)
      (fin_mul_inf hgF hx) (fin_mul_inf hjF hx) h
  have hcloc : cLoc w₀ (s⁻¹ * γ * s) = cLoc w₀ j * (cLoc w₀ c)⁻¹ * (cLoc w₀ j)⁻¹ := by
    have e : s⁻¹ * γ * s = g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ := by
      rw [hγeq]; group
    rw [e]
    simp only [map_mul, map_inv, hg1, hg1', hx1, inv_one, one_mul, mul_one]
  have hin : cLoc w₀ (s⁻¹ * γ * s) ∈ J n := by
    rw [hcloc]
    exact hJ.normal n _ hjJ _ (inv_mem hcJ)
  have hγ1 : γ = 1 := by
    by_contra hne'
    have hγZ : γ ∈ P '' D :=
      ⟨(s, g, g', j * c⁻¹ * j⁻¹, x⁻¹),
        ⟨hsS, hg, hg', mul_mem (mul_mem hjC0 (inv_mem hcC0)) (inv_mem hjC0), inv_mem hx⟩, hγeq.symm⟩
    exact hn₀ n hn _ ⟨(s, γ), ⟨hsS, ⟨hγZ, hγ⟩, hne'⟩, rfl⟩ hin
  subst hγ1
  have h2 : g' = g * x * c := by
    have : s * j * g' = s * j * (g * x * c) := by
      rw [h]; group
    exact mul_left_cancel this
  have hxF : x ∈ finU (E := E) (n := a) := by
    have e : x = g⁻¹ * g' * c⁻¹ := by
      rw [h2]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hgF) hgF') (inv_mem hcF)
  have hxe : x = 1 := eq_one_of_fin_inf hxF hx
  subst hxe
  have h3 : g⁻¹ * g' = c := by
    rw [h2]; group
  have hcK : c ∈ K := hck c hc (by
    rw [← h3, map_mul, map_inv, hg1, hg1', inv_one, one_mul])
  exact hinj g hg g' hg' (h3 ▸ hcK)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.ell_pf :
    UpperTheory.Gal.Gen.EllGrp → UpperTheory.Gal.Gen.Ell := by
  intro hGrp E _ _ _ n C hLev H _ lam hU2 hfin
  have hC := hLev.fin
  have hCc := hLev.compact
  obtain ⟨U1, hU1o, hU11, hU1C⟩ := hLev.isOpen
  obtain ⟨U2, hU2o, hU21, hU2l⟩ := hU2
  set D : Subgroup (UA E n) := C ⊔ infU E n with hDdef
  have hDC : D ≤ C.comap GlobalTheory.EllU.finPart := sup_le (fun c hc => by
      change GlobalTheory.EllU.finPart c ∈ C
      rw [GlobalTheory.EllU.finPart_of_finU (hC hc)]; exact hc)
    (fun x hx => by
      change GlobalTheory.EllU.finPart x ∈ C
      rw [GlobalTheory.EllU.finPart_of_infU hx]; exact C.one_mem)
  let f : D →* C := (GlobalTheory.EllU.finPart.comp D.subtype).codRestrict C (fun d => hDC d.2)
  let lam' : D →* H := lam.comp f
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E n
  have hI : IsCompact (infU E n : Set (UA E n)) := isCompact_iff_compactSpace.2 inferInstance
  have hDc : IsCompact (D : Set (UA E n)) := by
    rw [hDdef, Subgroup.mul_normal]
    exact hCc.mul hI
  have hyp : ∀ g : UA E n, ∀ γ ∈ ratU E n, ∀ d : D, γ * g = g * d → lam' d = 1 := by
    intro g γ hγ d h
    have hγ' : g * (d : UA E n) * g⁻¹ ∈ ratU E n := by
      rw [← h, mul_inv_cancel_right]; exact hγ
    have hd : IsOfFinOrder (d : UA E n) := GlobalTheory.T.isOfFinOrder_of_compact_conj_mem_unitaryRationalPoints E n D hDc g d d.2 hγ'
    obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hd
    have hdm : d ^ m = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hpow]; rfl)
    exact hfin (f d) (isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, by rw [← map_pow, hdm, map_one]⟩)
  obtain ⟨ℓ, h1, h2⟩ := hGrp (UA E n) H (ratU E n) D lam' hyp
  have hinf : ∀ g, ∀ x ∈ infU E n, ℓ (g * x) = ℓ g := by
    intro g x hx
    have e : f ⟨x, le_sup_right (a := C) hx⟩ = 1 := Subtype.ext (GlobalTheory.EllU.finPart_of_infU hx)
    have := h2 g ⟨x, le_sup_right (a := C) hx⟩
    simp only [lam', MonoidHom.comp_apply, e, map_one, mul_one] at this
    exact this
  have hC' : ∀ g (c : C), ℓ (g * c) = ℓ g * lam c := by
    intro g c
    have e : f ⟨c, le_sup_left (b := infU E n) c.2⟩ = c := Subtype.ext (GlobalTheory.EllU.finPart_of_finU (hC c.2))
    have := h2 g ⟨c, le_sup_left (b := infU E n) c.2⟩
    simp only [lam', MonoidHom.comp_apply, e] at this
    exact this
  set Wn : Set (UA E n) := GlobalTheory.EllU.finPart ⁻¹' (U1 ∩ U2) with hWn
  have hWo : IsOpen Wn := (hU1o.inter hU2o).preimage GlobalTheory.EllU.continuous_finPart
  have hW1 : (1 : UA E n) ∈ Wn := by
    change GlobalTheory.EllU.finPart 1 ∈ U1 ∩ U2
    rw [map_one]; exact ⟨hU11, hU21⟩
  have hWinv : ∀ g, ∀ w ∈ Wn, ℓ (g * w) = ℓ g := by
    intro g w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hkC : GlobalTheory.EllU.finPart w ∈ C := hU1C ⟨hw1, GlobalTheory.EllU.finPart_mem w⟩
    have hl : lam ⟨GlobalTheory.EllU.finPart w, hkC⟩ = 1 := hU2l ⟨GlobalTheory.EllU.finPart w, hkC⟩ hw2
    have e : g * w = g * GlobalTheory.EllU.finPart w * ((GlobalTheory.EllU.finPart w)⁻¹ * w) := by group
    rw [e, hinf _ _ (GlobalTheory.EllU.inv_finPart_mul_mem w)]
    have := hC' g ⟨GlobalTheory.EllU.finPart w, hkC⟩
    rw [hl, mul_one] at this
    exact this
  refine ⟨ℓ, hinf, hC', fun φ => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    refine (continuousAt_const (y := φ (ℓ g))).congr ?_
    have hc : Continuous fun y : UA E n => g⁻¹ * y := continuous_const.mul continuous_id
    have hm : Wn ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact hWo.mem_nhds hW1
    filter_upwards [hc.continuousAt.preimage_mem_nhds hm] with y hy
    change φ (ℓ g) = φ (ℓ y)
    have := hWinv g _ hy
    rw [mul_inv_cancel_left] at this
    rw [this]
  · intro γ hγ g
    change φ (ℓ (γ * g)) = φ (ℓ g)
    rw [h1 γ hγ g]
  · let S : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k | RU E n k (fun g => φ (ℓ g)) = fun g => φ (ℓ g)}
        one_mem' := by
          change RU E n 1 _ = _
          rw [map_one]; rfl
        mul_mem' := fun {a b} ha hb => by
          change RU E n ((a : UA E n) * b) _ = _
          rw [map_mul, Module.End.mul_apply]
          change RU E n a (RU E n b _) = _
          rw [hb, ha]
        inv_mem' := fun {a} ha => by
          change RU E n ((a : UA E n)⁻¹) _ = _
          conv_lhs => rw [← ha]
          change RU E n ((a : UA E n)⁻¹) (RU E n a _) = _
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    change IsOpen (S : Set (finU (E := E) (n := n)))
    refine Subgroup.isOpen_of_mem_nhds S (g := 1) ?_
    have ho : IsOpen ((Subtype.val : finU (E := E) (n := n) → UA E n) ⁻¹' Wn) := hWo.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho.mem_nhds hW1) fun k hk => ?_
    change RU E n k _ = _
    funext g
    change φ (ℓ (g * k)) = φ (ℓ g)
    rw [hWinv g _ hk]
  · refine FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton (fun g => φ (ℓ g))).subset ?_)
    rintro _ ⟨k, rfl⟩
    change RU E n k _ = _
    funext g
    change φ (ℓ (g * k)) = φ (ℓ g)
    rw [hinf g k k.2]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.tower_pf :
    UpperTheory.Gal.Gen.CongSub → UpperTheory.Gal.Gen.Tower := by
  intro hC E _ _ w a l hl hw ha N hN
  obtain ⟨m, -, J', lam, hJo, hJc, hJN, hJtf, -, -⟩ := GlobalTheory.T.exists_supercuspidal_type_character_zmod_pow E w a l hl hw ha N hN 0
  obtain ⟨J, hT, hp⟩ := hC E w a l hl hw
  obtain ⟨s, hs⟩ := hT.small _ (hJo.mem_nhds J'.one_mem)
  refine ⟨fun n => J (s + n), ⟨fun n => hT.isOpen _, fun n => hT.compact _, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hij
    exact hT.anti (Nat.add_le_add_left hij s)
  · intro n g hg x hx
    exact hT.normal (s + n) g (hT.anti (Nat.zero_le (s + 0)) hg) x hx
  · intro M hM
    obtain ⟨n, hn⟩ := hT.small M hM
    exact ⟨n, fun x hx => hn (hT.anti (Nat.le_add_left n s) hx)⟩
  · exact fun x hx => hJN (hs hx)
  · exact fun g hg ho => hJtf g (hs hg) ho
  · intro n x hx
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ, pow_mul]
      exact hp (s + n) _ ih
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound

private def sz {a : ℕ} (lam : DomWeight a) : ℕ := ∑ k, (lam.w k).natAbs

private theorem sz_dual {a : ℕ} (lam : DomWeight a) : sz lam.dual = sz lam := by
  unfold sz DomWeight.dual
  simp only [Int.natAbs_neg]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun k => by simp)

private theorem one_le {a : ℕ} (lam : DomWeight a) :
    ∑ i, lam.natW i + a * lam.detShift.natAbs ≤ a * (2 * sz lam) := by
  have key : ∀ i : Fin a, lam.natW i + lam.detShift.natAbs ≤ 2 * sz lam := by
    intro i
    have ha : 0 < a := i.pos
    have hd : lam.detShift = lam.w ⟨a - 1, by omega⟩ := by
      simp only [DomWeight.detShift, dif_pos ha]
    have hnat : lam.natW i = (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat := by
      simp only [DomWeight.natW, hd]
    have hLle : (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam := by
      unfold sz
      exact Finset.single_le_sum (f := fun k => (lam.w k).natAbs) (fun k _ => Nat.zero_le _)
        (Finset.mem_univ _)
    rw [hnat, hd]
    by_cases hi : i = ⟨a - 1, by omega⟩
    · have h0 : (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat = 0 := by
        rw [hi, sub_self]; rfl
      omega
    · have hpair : (lam.w i).natAbs + (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam := by
        unfold sz
        have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => (lam.w k).natAbs)
          (Finset.subset_univ {i, ⟨a - 1, by omega⟩}) (fun _ _ _ => Nat.zero_le _)
        rwa [Finset.sum_pair hi] at h
      omega
  calc ∑ i, lam.natW i + a * lam.detShift.natAbs
      = ∑ i, (lam.natW i + lam.detShift.natAbs) := by
        simp [Finset.sum_add_distrib]
    _ ≤ ∑ _i : Fin a, 2 * sz lam := Finset.sum_le_sum fun i _ => key i
    _ = a * (2 * sz lam) := by simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

private noncomputable def emb : InfinitePlace E ⊕ InfinitePlace E → (E →+* ℂ)
  | .inl v => v.embedding
  | .inr v => ComplexEmbedding.conjugate v.embedding

private theorem mk_emb_inl (v : InfinitePlace E) : InfinitePlace.mk (emb (.inl v)) = v :=
  InfinitePlace.mk_embedding v

private theorem mk_emb_inr (v : InfinitePlace E) : InfinitePlace.mk (emb (.inr v)) = v := by
  simp [emb]

private theorem emb_injective : Function.Injective (emb (E := E)) := by
  intro x y h
  have hm : InfinitePlace.mk (emb x) = InfinitePlace.mk (emb y) := by rw [h]
  rcases x with v | v <;> rcases y with w | w <;>
    simp only [mk_emb_inl, mk_emb_inr] at hm <;> subst hm
  · rfl
  · simp only [emb] at h
    exact absurd h.symm (conjugate_ne _)
  · simp only [emb] at h
    exact absurd h (conjugate_ne _)
  · rfl

private theorem two_le (W : Wt E a) : ∑ v, 2 * sz (W v) ≤ GlobalTheory.CongW.wtSize W.at := by
  have h1 : ∑ v, 2 * sz (W v)
      = ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s)) := by
    rw [Fintype.sum_sum_type]
    simp only [emb, Wt.at_embedding, Wt.at_conjugate, sz_dual, two_mul, Finset.sum_add_distrib]
  have h2 : ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s))
      = ∑ τ ∈ Finset.univ.map ⟨emb, emb_injective⟩, sz (W.at τ) := by
    rw [Finset.sum_map]; rfl
  have h3 : GlobalTheory.CongW.wtSize W.at = ∑ τ, sz (W.at τ) := rfl
  rw [h1, h2, h3]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound

open UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound in
theorem UpperTheory.Gal.Gen.sizeLe_pf :
    UpperTheory.Gal.Gen.SizeLe := by
  intro E _ _ _ a W
  calc (∑ v, ∑ i, (W v).natW i) + ∑ v, a * (W v).detShift.natAbs
      = ∑ v, (∑ i, (W v).natW i + a * (W v).detShift.natAbs) := Finset.sum_add_distrib.symm
    _ ≤ ∑ v, a * (2 * sz (W v)) := Finset.sum_le_sum fun v _ => one_le (W v)
    _ = a * ∑ v, 2 * sz (W v) := by rw [Finset.mul_sum]
    _ ≤ a * GlobalTheory.CongW.wtSize W.at := Nat.mul_le_mul_left a (two_le W)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem totalDegree_le_of_col {r n : ℕ} {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) ℂ}
    (h : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν) : F.totalDegree ≤ ∑ i, ν i := by
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => ?_
  have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m = ν := h (MvPolynomial.mem_support_iff.mp hm)
  rw [← hw, Finsupp.weight_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul]
  rw [Finset.sum_comm]
  refine le_of_eq (Finset.sum_congr rfl fun v _ => ?_)
  simp [Pi.single_apply]

theorem UpperTheory.Gal.Gen.degLe_pf :
    UpperTheory.Gal.Gen.DegLe := by
  intro T _ n lam x hx
  refine Submodule.span_induction (p := fun x _ => MvPolynomial.totalDegree x ≤ ∑ τ, ∑ i, (lam τ).natW i)
    ?_ ?_ ?_ ?_ hx
  · rintro P ⟨F, hF, rfl⟩
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    refine (MvPolynomial.totalDegree_rename_le (fun v => (τ, v)) (F τ)).trans ?_
    have hm := (Submodule.mem_inf.mp (hF τ)).1
    exact totalDegree_le_of_col ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hm)
  · simp
  · intro a b _ _ ha hb
    exact (MvPolynomial.totalDegree_add a b).trans (max_le ha hb)
  · intro c a _ ha
    exact (MvPolynomial.totalDegree_smul_le c a).trans ha
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private lemma norm_det_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hR : 1 ≤ R) (h : ∀ i j, ‖ι.symm (M i j)‖ ≤ R) : ‖ι.symm M.det‖ ≤ R ^ n :=
  _root_.UpperTheory.Reformulated.B.Qh59.norm_det_le ι M R hR h

theorem UpperTheory.Gal.Gen.detBound_pf :
    UpperTheory.Gal.Gen.DetBound := by
  intro l _ ι T _ n lam A R hR h
  have hR0 : (0 : ℝ) ≤ R := zero_le_one.trans hR
  rw [Formalism.L2.DIV.detTw_eq, map_prod, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_
  have h1 := norm_det_le ι ((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) R hR fun i j => (h τ i j).1
  have h2 := norm_det_le ι (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) R hR fun i j => (h τ i j).2
  have hinv : (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det =
      (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [pow_mul]
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (lam τ).detShift
  · rw [hk, zpow_natCast, map_pow, norm_pow, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 k
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow, ← hinv, map_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 k
end
