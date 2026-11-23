module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorFunctionalGlobalFormsAbelianS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.TameStab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Groups

variable {G Γ : Type} [Group G] [Group Γ]

def conjIn (H J : Subgroup G) (g : G) : Subgroup G where
  carrier := {x | x ∈ H ∧ g⁻¹ * x * g ∈ J}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    have := J.mul_mem ha' hb'
    convert this using 1
    group
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, ?_⟩
    have := J.inv_mem ha'
    convert this using 1
    group

def conjInEquiv (H J : Subgroup G) (g : G) : {γ : H // g⁻¹ * (γ : G) * g ∈ J} ≃ conjIn H J g where
  toFun γ := ⟨γ.1.1, γ.1.2, γ.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_conj (ι : Γ →* G) (J : Subgroup G) {I : Type} (y : I → G) (hrep : Bridge.IsReps ι J y)
    (hfin : ∀ i, Finite (Bridge.stab ι J (y i))) (g : G) : Finite {γ : ι.range // g⁻¹ * (γ : G) * g ∈ J} := by
  obtain ⟨c, ⟨γ₀, k, hg⟩, -⟩ := hrep g
  haveI := hfin c
  let f : Bridge.stab ι J (y c) → {γ : ι.range // g⁻¹ * (γ : G) * g ∈ J} := fun s =>
    ⟨⟨ι (γ₀ * s * γ₀⁻¹), γ₀ * s * γ₀⁻¹, rfl⟩, by
      have hs : (y c)⁻¹ * ι s * (y c) ∈ J := by
        have := s.2
        simpa [Bridge.stab, Subgroup.mem_comap, MulAut.conj_apply] using this
      have := J.mul_mem (J.mul_mem (J.inv_mem k.2) hs) k.2
      convert this using 1
      rw [hg]
      simp only [map_mul, map_inv]
      group⟩
  refine Finite.of_surjective f ?_
  rintro ⟨⟨_, a, rfl⟩, ha⟩
  refine ⟨⟨γ₀⁻¹ * a * γ₀, ?_⟩, ?_⟩
  · have := J.mul_mem (J.mul_mem k.2 ha) (J.inv_mem k.2)
    simp only [Bridge.stab, Subgroup.mem_comap, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv]
    convert this using 1
    rw [hg]
    simp only [map_mul, map_inv]
    group
  · apply Subtype.ext
    apply Subtype.ext
    show ι (γ₀ * (γ₀⁻¹ * a * γ₀) * γ₀⁻¹) = ι a
    congr 1
    group

end Groups



theorem rat_eq_one {D : D7} (V : TH.HSp D) (l : ℕ) (hl : l.Prime) (hN : V.rank + 1 < l)
    (hirr : Irreducible (Polynomial.cyclotomic l D.host.E)) (x : Bridge.Gf V) (hx : x ∈ (Bridge.ratF V).range)
    (hxl : x ^ l = 1) : x = 1 := by
  obtain ⟨q, rfl⟩ := hx
  have hq := q.2
  simp only [Formalism.L2.Theta.GQ, GlobalTheoryTheory.GenusMassVolumes.HFinIn, Subgroup.mem_subgroupOf, GlobalTheoryTheory.GenusMassVolumes.HFin, Subgroup.mem_map] at hq
  obtain ⟨u, -, hu⟩ := hq
  let φ : D.host.E →+* GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom.comp
      (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F))
  have key : ((Bridge.ratF V q : Bridge.Gf V) : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val = u.val.map φ := by
    have hu' : (q.1 : Formalism.L2.Theta.GA D V).1 =
        Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) u := hu.symm
    have h1 : ((Bridge.ratF V q : Bridge.Gf V) : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
        Formalism.UG.bc (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
          (q.1 : Formalism.L2.Theta.GA D V).1 := rfl
    rw [h1, hu']
    ext i j
    rfl
  rcases subsingleton_or_nontrivial (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) with hs | hs
  · apply Subtype.ext
    apply Units.ext
    ext i j
    exact Subsingleton.elim _ _
  · have hφ : Function.Injective φ := φ.injective
    have h2 := congrArg (fun z : Bridge.Gf V => (z : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val) hxl
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one] at h2
    rw [key] at h2
    have h3 : φ.mapMatrix (u.val ^ l) = φ.mapMatrix 1 := by
      rw [map_pow, map_one, RingHom.mapMatrix_apply]
      exact h2
    have hu1 : u.val ^ l = 1 := Matrix.map_injective hφ h3
    have hu2 : u.val = 1 :=
      GlobalTheory.no_order_l_of_cyclotomic_irreducible D.host.E l V.rank _ hl hirr hN hu1
    apply Subtype.ext
    apply Units.ext
    rw [key, hu2]
    have h4 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map φ = 1 := Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)
    rw [h4]
    rfl

theorem tameAt_of_smallAt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m)
    (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hNr : P.Nr = (Vc D j).rank) (hS : SmallAt p j P w) :
    TameAt p j w := by
  obtain ⟨hl, hN, hd, -, -⟩ := hS
  intro g
  have hfin : Finite {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)} :=
    finite_conj (Bridge.ratF (Vc D j)) (levJ p j (p.R.mu w)) (p.R.B.L j (p.R.mu w)).pres.y (p.R.B.L j (p.R.mu w)).pres.reps
      (fun c => Finite.of_equiv _ ((p.R.B.L j (p.R.mu w)).pres.stabI c).toEquiv) g
  refine ⟨hfin, ?_⟩
  intro hdvd
  haveI : Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime := ⟨hl⟩
  rw [Nat.card_congr (conjInEquiv _ _ g)] at hdvd
  haveI : Finite (conjIn (Bridge.ratF (Vc D j)).range (levJ p j (p.R.mu w)) g) := Finite.of_equiv _ (conjInEquiv _ _ g)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (Formalism.EigenvalueLevelCeiling.plc w) hdvd
  have hirr := GlobalTheory.cyclotomic_irreducible_of_not_dvd_discr D.host.E (Formalism.EigenvalueLevelCeiling.plc w) hl hd
  have hxl : (x : Bridge.Gf (Vc D j)) ^ (Formalism.EigenvalueLevelCeiling.plc w) = 1 := by
    rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one]
    rfl
  have h1 := rat_eq_one (Vc D j) (Formalism.EigenvalueLevelCeiling.plc w) hl (hNr ▸ hN) hirr x x.2.1 hxl
  have hx1 : x = 1 := Subtype.ext h1
  rw [hx1, orderOf_one] at hx
  exact hl.one_lt.ne hx

end GlobalTheory.TameStab

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem perm_of_isDC {G : Type} [Group G] (J : Subgroup G) (x : G) (A : Finset G) (h : Bridge.IsDC J x A) (κ : G)
    (hκ : κ ∈ J) : ∃ σ : Equiv.Perm A, ∀ s : A, ((σ s : A) : G)⁻¹ * κ * s ∈ J := by
  classical
  have hex : ∀ s : A, ∃ a : A, (a : G)⁻¹ * (κ * s) ∈ J := by
    intro s
    obtain ⟨k₁, k₂, hs⟩ := h.1 s s.2
    obtain ⟨a, ⟨ha, haJ⟩, -⟩ := h.2 (κ * s) ⟨⟨κ, hκ⟩ * k₁, k₂, by rw [hs]; simp [mul_assoc]⟩
    exact ⟨⟨a, ha⟩, haJ⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro s s' hss
    have h1 := hf s
    have h2 := hf s'
    rw [hss] at h1
    have h3 : (s : G)⁻¹ * s' ∈ J := by
      have := J.mul_mem (J.inv_mem h1) h2
      simpa [mul_assoc] using this
    obtain ⟨k₁, k₂, hs'⟩ := h.1 s' s'.2
    have hu := (h.2 s' ⟨k₁, k₂, hs'⟩).unique ⟨s.2, h3⟩ ⟨s'.2, by simp [J.one_mem]⟩
    exact Subtype.ext hu
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun s => ?_⟩
  simpa [mul_assoc] using hf s

theorem map_ev_eq_one_of_loc : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → ((l : ℕ) : 𝓞 D.host.E) ∉ (pl i.1.1).asIdeal → isLocEnv V pl ok i x → ((x : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map ev = 1 := by
  intro D V Pl0 pl ok i x l _ inc ev hev hl hx
  obtain ⟨e, α, he, -, hs, hxα⟩ := hx
  obtain ⟨v, ε, ⟨a, rfl, -, ha⟩, hf, hv⟩ := GlobalTheory.VacLat.place_of_primeIdem (Or.inl ⟨he, rfl⟩)
  have h0 : ev (a ⊗ₜ[D.host.F] 1) = 0 := by
    refine hev.2.2.1 a fun v' hv' => ha v' ?_
    rintro rfl
    apply hl
    rw [← hv] at hv'
    have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((l : ℕ) : 𝓞 D.host.F) ∈ (pl i.1.1).asIdeal := hv'
    rwa [map_natCast] at h1
  have h2 := GlobalTheory.SplitHeckeAdj.map_eq_one_of_supp (ev.comp (Formalism.L2.Theta.finPart D)) (e + Formalism.L2.Theta.cA D e)
    (by rw [hf]; exact h0) (Formalism.L2.Theta.mt V α) hs
  rw [hxα]
  exact h2

theorem chi_move {G : Type} [Group G] (J Lc : Subgroup G) (χ : J →* ℂˣ)
    (l2 : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ l ∈ Lc, Commute k₂ l)
    (l3 : ∀ k : J, (k : G) ∈ Lc → χ k = 1) (κ κ' : J) (a s : G) (ha : a ∈ Lc) (hs : s ∈ Lc)
    (h : (κ' : G) = a⁻¹ * κ * s) : χ κ' = χ κ := by
  obtain ⟨k₁, h₁, k₂, h₂, hL, hk, hc⟩ := l2 κ κ.2
  have e1 : κ = ⟨k₁, h₁⟩ * ⟨k₂, h₂⟩ := Subtype.ext hk
  have e2 : ((κ' * (⟨k₂, h₂⟩ : J)⁻¹ : J) : G) = a⁻¹ * k₁ * s := by
    show (κ' : G) * k₂⁻¹ = _
    rw [h, hk, mul_assoc a⁻¹, mul_assoc k₁, (hc s hs).eq]; group
  have e3 := l3 (κ' * (⟨k₂, h₂⟩ : J)⁻¹) (e2 ▸ Lc.mul_mem (Lc.mul_mem (Lc.inv_mem ha) hL) hs)
  rw [map_mul, map_inv, mul_inv_eq_one] at e3
  rw [e3, e1, map_mul, l3 ⟨k₁, h₁⟩ hL, one_mul]



theorem levChi_eq_of_loc : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ∀ (κ κ' : levJ p j t) (a s : Bridge.Gf (Vc D j)), a ∈ hkA p j t i → s ∈ hkA p j t i → (κ' : Bridge.Gf (Vc D j)) = a⁻¹ * κ * s → levChi p j t κ' = levChi p j t κ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t i h1 h2 κ κ' a s ha hs h
  have hb := p.charW.base
  have ha' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i a := (p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩ a ha
  have hs' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i s := (p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩ s hs
  refine hb.fam.tie.elim fun _ x => x.elim fun _ x => x.elim fun _ tie => ?_
  refine (hb.lev.βV j).elim fun c hc => ?_
  rw [one_pow] at hc
  refine ha'.elim fun e x => x.elim fun _ x => ?_
  have he := x.1
  have hsp := (tie.ok t _).1 (show (p.P.A3.A.ok t) × ℕ from i).1.2
  have hl := GlobalTheory.SplitHeckeAdj.local_group (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) hc _ e he
    fun PP hP => GlobalTheory.SplitHeckeAdj.off_of_splitOff hsp PP (hP.elim (fun h1 => Or.inl (hb.fam.Sb h1)) Or.inr)
  refine hl.elim fun Lc l => ?_
  have hA : a ∈ Lc := (GlobalTheory.SplitHeckeAdj.loc_supp _ ha' he).elim fun g hg => hg.2 ▸ l.1 g hg.1
  have hS : s ∈ Lc := (GlobalTheory.SplitHeckeAdj.loc_supp _ hs' he).elim fun g hg => hg.2 ▸ l.1 g hg.1
  exact chi_move _ Lc _ l.2.1 l.2.2.1 κ κ' a s hA hS h

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem chi_cancel {K R : Type} [Field K] [CommRing R] (io : K ≃+* ℂ) (emb : R →+* K) (hinj : Function.Injective emb)
    (u u' : Rˣ) (X X' : K) (hXX : X' = X) (hX : X ≠ 0) (c c' : ℂ) (hcc : c' = c) (hc : c ≠ 0)
    (e1 : io (emb u' * X') * c' = 1) (e2 : io (emb u * X) * c = 1) : u' = u := by
  subst hXX hcc
  have e4 := io.injective (mul_right_cancel₀ hc (e1.trans e2.symm))
  exact Units.ext (hinj (mul_right_cancel₀ hX e4))

theorem perm_core (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ)
    (hR : 1 ≤ i.2 ∧ i.2 ≤ (Vc D j).rank) (κ : levJ p j t) :
    ∃ σ : Equiv.Perm (hkA p j t i), ∀ s : hkA p j t i, ((σ s : hkA p j t i) : Bridge.Gf (Vc D j))⁻¹ * κ * s ∈ levJ p j t := by
  have h : Bridge.IsDC (levJ p j t) ((p.R.B.L j t).hecke.hx i) (hkA p j t i) := (p.R.B.L j t).hecke.hDC i hR
  exact perm_of_isDC (levJ p j t) ((p.R.B.L j t).hecke.hx i) (hkA p j t i) h κ κ.2

theorem perm_gen (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (io : PadicAlgCl l ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))
    (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j t →* (intR Lf)ˣ)
    (hev : ∀ τ, EvOk (incOf D e0 b τ) (ev τ)) (hkap : KapEq p j t ev bs rk kap) (hchi : ChiEq p j t io sh kap chi)
    (i : Ix p j t l N) (κ : levJ p j t) :
    ∃ σ : Equiv.Perm (hkA p j t i.1), ∀ s : hkA p j t i.1, ∃ κ' : levJ p j t,
      (κ : Bridge.Gf (Vc D j)) * (s : Bridge.Gf (Vc D j)) = (σ s : Bridge.Gf (Vc D j)) * κ' ∧ kap κ' = kap κ ∧
        chi κ' = chi κ := by
  have hN : N = (Vc D j).rank := Fin.equiv_iff_eq.mp ⟨rk.toEquiv⟩
  have hR : 1 ≤ i.1.2 ∧ i.1.2 ≤ (Vc D j).rank := ⟨i.2.1, by rw [← hN]; exact i.2.2.1⟩
  have hp := perm_core p j t i.1 hR κ
  refine hp.elim fun σ hσ => ?_
  have hinj : Function.Injective (intEmb Lf) := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have loc : ∀ y ∈ hkA p j t i.1, ∀ τ,
      ((y : GL (Fin (Vc D j).rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) = 1 := by
    intro y hy τ
    have hy' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i.1 y := (p.R.B.L j t).hecke.hA_loc i.1 hR y hy
    exact map_ev_eq_one_of_loc (Vc D j) p.R.pl (p.P.A3.A.ok t) i.1 y _ (ev τ) (hev τ) i.2.2.2 hy'
  have key : ∀ (κ' : levJ p j t) (a s : Bridge.Gf (Vc D j)), a ∈ hkA p j t i.1 → s ∈ hkA p j t i.1 →
      (κ' : Bridge.Gf (Vc D j)) = a⁻¹ * κ * s → kap κ' = kap κ ∧ chi κ' = chi κ := by
    intro κ' a s ha hs he
    have hmap : ∀ τ, (((κ' : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) =
        (((κ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) := by
      intro τ
      have ha1 := loc a ha τ
      have hs1 := loc s hs τ
      have ha' : ((((a⁻¹ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
          (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) = 1 := by
        have h0 : ((((a⁻¹ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
            (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) *
            (((a : GL (Fin (Vc D j).rank)
            (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) = 1 := by
          rw [← Matrix.map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
            Matrix.map_one _ (ev τ).map_zero (ev τ).map_one]
        rwa [ha1, mul_one] at h0
      rw [he]
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha', hs1, one_mul, mul_one]
    have hmat : ∀ τ, kapMat p j t ev bs rk κ' τ = kapMat p j t ev bs rk κ τ := by
      intro τ
      unfold kapMat matOf
      rw [hmap τ]
    have hK : kap κ' = kap κ := by
      funext τ
      apply Units.ext
      apply Matrix.ext
      intro a c
      apply hinj
      have h1 := (hkap κ' τ).trans ((hmat τ).trans (hkap κ τ).symm)
      exact congrFun (congrFun h1 a) c
    refine ⟨hK, ?_⟩
    have hL := levChi_eq_of_loc p j t i.1 hR.1 hR.2 κ κ' a s ha hs he
    have hX : (∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ ?_
      exact ((Matrix.GeneralLinearGroup.det (kap κ τ)).isUnit.map (intEmb Lf)).ne_zero
    have hXX : (∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) = ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ :=
      congrArg (fun f : D.what₂.Tau → GL (Fin N) (intR Lf) => ∏ τ, intEmb Lf (f τ).val.det ^ sh τ) hK
    have hcc : ((levChi p j t κ' : ℂˣ) : ℂ) = ((levChi p j t κ : ℂˣ) : ℂ) := congrArg (fun z : ℂˣ => (z : ℂ)) hL
    have e1 : io (intEmb Lf (chi κ') * ∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) * ((levChi p j t κ' : ℂˣ) : ℂ) = 1 :=
      hchi κ'
    have e2 : io (intEmb Lf (chi κ) * ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) * ((levChi p j t κ : ℂˣ) : ℂ) = 1 :=
      hchi κ
    exact chi_cancel io (intEmb Lf) hinj (chi κ) (chi κ') (∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ)
      (∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) hXX hX ((levChi p j t κ : ℂˣ) : ℂ) ((levChi p j t κ' : ℂˣ) : ℂ) hcc
      (levChi p j t κ).ne_zero e1 e2
  refine ⟨σ, fun s => ⟨⟨((σ s : hkA p j t i.1) : Bridge.Gf (Vc D j))⁻¹ * κ * s, hσ s⟩, ?_, ?_, ?_⟩⟩
  · show (κ : Bridge.Gf (Vc D j)) * s = (σ s : Bridge.Gf (Vc D j)) * ((σ s : Bridge.Gf (Vc D j))⁻¹ * κ * s)
    group
  · exact (key _ _ _ (σ s).2 s.2 rfl).1
  · exact (key _ _ _ (σ s).2 s.2 rfl).2



open Classical in
theorem permAt (p : PtAt ex Csz) (j : Fin D.R.m) (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    PermAt p j P w := by
  intro _ e0 b io ev bs rk sh Lf _ kap chi hC
  obtain ⟨-, -, -, hev, hkap, hchi⟩ := hC
  dsimp only [GlobalTheory.FrameOf.frameOf]
  intro i κ
  exact perm_gen p j (p.R.mu w) e0 b io ev bs rk sh Lf kap chi hev hkap hchi i κ

end Point

end GlobalTheory.FramePerm
end
end

section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameAutCof

theorem sub_mem_of_prime_norm {K : Type} [Field K] [NumberField K] (σ : 𝓞 K →+* 𝓞 K) (I : Ideal (𝓞 K))
    (hp : (Ideal.absNorm I).Prime) (hI : I.map σ ≤ I) (x : 𝓞 K) : σ x - x ∈ I := by
  have hc : Nat.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Fact (Ideal.absNorm I).Prime := ⟨hp⟩
  have : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  have := Fintype.ofFinite (𝓞 K ⧸ I)
  let e := ZMod.ringEquivOfPrime (𝓞 K ⧸ I) hp (by rw [← Nat.card_eq_fintype_card, hc])
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (e.symm (Ideal.Quotient.mk I x))
  have h1 : x - (n : 𝓞 K) ∈ I := by
    rw [← Ideal.Quotient.eq, map_intCast]
    apply e.symm.injective
    rw [map_intCast, hn]
  have h2 : σ x - (n : 𝓞 K) ∈ I := by
    have := hI (Ideal.mem_map_of_mem σ h1)
    rwa [map_sub, map_intCast] at this
  have := I.sub_mem h2 h1
  rwa [sub_sub_sub_cancel_right] at this

theorem finite_fixed {K : Type} [Field K] [NumberField K] [StarRing K] (h : ∃ x : K, star x ≠ x) :
    {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal).Prime ∧ Formalism.DivisionValues.conjPl v = v}.Finite := by
  have hx : ∃ x : 𝓞 K, Formalism.DivisionValues.cO K x - x ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨y, hy⟩ := h
    apply hy
    have h0 : ∀ a : 𝓞 K, star (a : K) = a := fun a => congrArg (fun z : 𝓞 K => (z : K)) (sub_eq_zero.1 (hn a))
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
    rw [star_div₀]
    exact congrArg₂ (· / ·) (h0 a) (h0 b)
  obtain ⟨x, hx⟩ := hx
  refine (Ideal.finite_factors (I := Ideal.span {Formalism.DivisionValues.cO K x - x}) (by simpa using hx)).subset ?_
  rintro v ⟨hp, hv⟩
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  exact sub_mem_of_prime_norm (Formalism.DivisionValues.cO K : 𝓞 K →+* 𝓞 K) v.asIdeal hp
    (le_of_eq (congrArg HeightOneSpectrum.asIdeal hv)) x

theorem exists_star_ne (D : D7) : ∃ x : D.host.E, star x ≠ x := by
  by_contra hn
  push Not at hn
  apply IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => ?_
  exact hn x

theorem cofinite_labels {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (t : p.P.T) {l : ℕ} (hl : l ≠ 0) :
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (GlobalTheory.ExpTie.blk p j t).Pl, ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t Q).asIdeal ∧ labOf p j t Q = v}.Finite := by
  obtain ⟨gR, c0R, c0L, hTie⟩ := p.charW.base.fam.tie
  have honto := p.charW.base.fam.pl_onto
  have hcc : ∀ v : HeightOneSpectrum (𝓞 D.host.E), Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl v) = v := Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl
  have hinj : Function.Injective (Formalism.DivisionValues.conjPl (K := D.host.E)) := Function.Involutive.injective hcc
  set S : Set (HeightOneSpectrum (𝓞 D.host.E)) := (p.R.Sb : Set (Pl D.host.E)) ∪ (p.R.Q t : Set (Pl D.host.E)) with hS
  have hSf : S.Finite := hTie.S_fin.union (Finset.finite_toSet _)
  have hlf : {v : HeightOneSpectrum (𝓞 D.host.E) | v.asIdeal ∣ Ideal.span {((l : ℕ) : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa using hl)
  refine (((finite_fixed (exists_star_ne D)).union hSf).union ((hSf.union hlf).preimage hinj.injOn)).subset ?_
  rintro v ⟨hp, hv⟩
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, not_or, not_and, Ideal.dvd_span_singleton] at hn
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hn
  have hci : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (Formalism.DivisionValues.conjPl v).asIdeal = v.asIdeal := by
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hcc]
  have hoff : Bridge.SplitOff (D := D) (Formalism.DivisionValues.conjPl v) S := by
    refine ⟨?_, h3, fun Q hQ he => h2 ?_⟩
    · rw [hci]
      exact fun he => h1 hp (HeightOneSpectrum.ext he).symm
    · rw [hci] at he
      exact HeightOneSpectrum.ext he ▸ hQ
  obtain ⟨P, hP⟩ := honto (Formalism.DivisionValues.conjPl v) ⟨hoff.1, fun h => hoff.2.1 (Or.inl h), fun Q hQ => hoff.2.2 Q (Or.inl hQ)⟩
  have hok := (hTie.ok t P).2 (hP ▸ hoff)
  have e1 : plOf p j t ⟨P, hok⟩ = Formalism.DivisionValues.conjPl v := hP
  refine hv ⟨⟨P, hok⟩, ?_, ?_⟩
  · rw [e1]; exact h4
  · show Formalism.DivisionValues.conjPl (plOf p j t ⟨P, hok⟩) = v
    rw [e1, hcc]

end GlobalTheory.FrameAutCof
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_tangentVector_functional_globalForms_abelianScheme : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ φ : Form (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, (∀ f, GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → φ f = 0) → ∃ v : epsR R ⟶ A, IsTangent v ∧ ∀ f, tanVal v f = φ f := by
  first | exact @GlobalTheory.LieDual.exists_tangent_of_functional | exact GlobalTheory.LieDual.exists_tangent_of_functional | (intros; apply GlobalTheory.LieDual.exists_tangent_of_functional <;> assumption)
end
