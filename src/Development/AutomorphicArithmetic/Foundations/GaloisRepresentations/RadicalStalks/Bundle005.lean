module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.Ord.DimsAlg

variable {k : Type} [Field k] {C : Type} [CommRing C]

private abbrev W (ν : C → k) : Submodule k (k ⊗[ℤ] C) :=
  ⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (ν c)

private theorem mem_W (ν : C → k) (x : k ⊗[ℤ] C) :
    x ∈ W ν ↔ ∀ c : C, ∃ n : ℕ, (((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) ^ n) * x = 0 := by
  simp only [W, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace]
  refine forall_congr' fun c => exists_congr fun n => ?_
  have h : (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c - ν c • (1 : Module.End k (k ⊗[ℤ] C)))
      = Algebra.lmul k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) := by
    have : ν c ⊗ₜ[ℤ] (1 : C) = ν c • (1 : k ⊗[ℤ] C) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [this, map_sub, map_smul, map_one]
    rfl
  rw [h, ← map_pow]
  rfl

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

private def frobZ : k ≃ₐ[ℤ] k := AlgEquiv.ofRingEquiv (f := frobeniusEquiv k p) (fun n => by simp)

private def E : (k ⊗[ℤ] C) ≃ₐ[ℤ] (k ⊗[ℤ] C) := Algebra.TensorProduct.congr (frobZ (k := k) p) AlgEquiv.refl

private theorem E_tmul (l : k) (c : C) : E p (l ⊗ₜ[ℤ] c) = (l ^ p) ⊗ₜ[ℤ] c := by
  simp [E, frobZ, frobenius_def]

private theorem E_smul (l : k) (x : k ⊗[ℤ] C) : E p (l • x) = l ^ p • E p x := by
  induction x with
  | tmul a c => simp [TensorProduct.smul_tmul', E_tmul, mul_pow]
  | add x y hx hy => simp [smul_add, hx, hy]

private theorem E_mem (ν : C → k) (x : k ⊗[ℤ] C) : E p x ∈ W (fun c => ν c ^ p) ↔ x ∈ W ν := by
  rw [mem_W, mem_W]
  refine forall_congr' fun c => exists_congr fun n => ?_
  have h : E p (((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) ^ n * x)
      = ((1 : k) ⊗ₜ[ℤ] c - (ν c ^ p) ⊗ₜ[ℤ] (1 : C)) ^ n * E p x := by
    rw [map_mul, map_pow, map_sub, E_tmul, E_tmul, one_pow]
  rw [← h]
  exact map_eq_zero_iff _ (E p).injective

private theorem finrank_W_pow (ν : C → k) :
    Module.finrank k ↥(W (fun c => ν c ^ p)) = Module.finrank k ↥(W ν) := by
  let j : ↥(W ν) ≃+ ↥(W (fun c => ν c ^ p)) :=
    { toFun := fun x => ⟨E p x.1, (E_mem p ν x.1).2 x.2⟩
      invFun := fun y => ⟨(E p).symm y.1, (E_mem p ν _).1 (by simpa using y.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hr := rank_eq_of_equiv_equiv (R := k) (R' := k) (M := ↥(W ν)) (M₁ := ↥(W (fun c => ν c ^ p)))
    (⟨fun l => l ^ p, by simp [(Fact.out : p.Prime).ne_zero]⟩ : ZeroHom k k) j
    (frobeniusEquiv k p).bijective (fun r m => Subtype.ext (E_smul p r m.1))
  exact (congrArg Cardinal.toNat hr).symm

end UpperTheory.Gal.Ord.DimsAlg

namespace UpperTheory.Gal.Ord.DimsCoh

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {k : Type} [Field k] {t : Sp k ⟶ Sp R}

private def cohHom (o : Obj b N t) : 𝓞 D.F →+* Module.End k (primDR o.A) :=
  RingHom.mk'
    { toFun := coh o
      map_one' := by
        haveI := o.act.hom
        refine LinearMap.ext fun x => ?_
        exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_id _ _ _ (by rw [map_one, o.act.one]) x
      map_mul' := fun x y => by
        haveI := o.act.hom
        refine LinearMap.ext fun c => ?_
        exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_comp _ _ _ _ _ (by rw [mul_comm x y, map_mul, o.act.mul]) c }
    fun x y => by
      haveI := o.act.hom
      refine LinearMap.ext fun c => ?_
      exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_mul _ _ _ _ _ (by rw [map_add (f := _), o.act.add]) c

end UpperTheory.Gal.Ord.DimsCoh

open UpperTheory.Gal.Ord.DimsAlg UpperTheory.Gal.Ord.DimsCoh in
theorem UpperTheory.Gal.Ord.dims :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ j : ℕ, Module.finrank k ↥(⨅ c, (coh o c).maxGenEigenspace (β (b.t i c) ^ p ^ j)) =
        Module.finrank k ↥(⨅ c, (coh o c).maxGenEigenspace (β (b.t i c))) := by
  intro p _ D R _ b N hN hNp _ k _ _ hk β o i w f _ _ _ π j
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o.A o.ab
  obtain ⟨hfd, -, -⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o.A g o.ab hg
  haveI := hfd
  haveI : Module.Finite k (primDR o.A) := (Module.finite_dual_iff k).1 hfd
  haveI := D.freeLa
  haveI := D.finLa
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hk
  obtain ⟨l, hlp, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : l.Coprime p := (Nat.coprime_primes hl (Fact.out : p.Prime)).2 (by omega)
  have hcopj : ∀ j : ℕ, (l ^ j).Coprime p := fun j => Nat.Coprime.pow_left j hcop
  have hposj : ∀ j : ℕ, 0 < l ^ j := fun j => pow_pos hl.pos j
  have hlk : (l : k) ≠ 0 := by
    have hu := (b.unit l hcop).map β
    rw [map_natCast] at hu
    exact hu.ne_zero
  obtain ⟨I, -⟩ := o.geom k (𝟙 _) β (by rw [Category.id_comp])
  have hc : ∀ c : 𝓞 D.F, LinearMap.charpoly (cohHom o c) =
      ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n)).map (Int.castRingHom k) := by
    intro c
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    have e := GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic k o.A o.ab (o.act.act (algebraMap (𝓞 D.F) D.O c)) D.La
      (DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) l hl hlk (fun j => I.ev (l ^ j))
      (fun j x y => I.add (l ^ j) x y) (fun j x => I.lin (l ^ j) _ x)
      (fun j x => I.ker (l ^ j) (hposj j) (hcopj j) x) (fun j q => I.onto (l ^ j) (hposj j) (hcopj j) q)
    rw [GlobalTheory.T.charpoly_la_eq_pow p D c] at e
    rw [← e]
    exact (GlobalTheory.DeRhamCharpolyP.charpoly_dualMap _).symm
  have key := fun χ : 𝓞 D.F →+* k => GlobalTheory.T.finrank_jointWeightSpace_eq_of_charpoly k (𝓞 D.F) ↥(primDR o.A) (cohHom o) (D.m * D.n) hc χ
  have e1 := key ((iterateFrobenius k p j).comp (β.comp (b.t i)))
  have e2 := key (β.comp (b.t i))
  have hW : ∀ (j : ℕ) , Module.finrank k ↥(W (C := 𝓞 D.F) (fun c => β (b.t i c) ^ p ^ j)) =
      Module.finrank k ↥(W (C := 𝓞 D.F) (fun c => β (b.t i c))) := by
    intro j
    induction j with
    | zero => exact congrArg (fun ν : 𝓞 D.F → k => Module.finrank k ↥(W ν)) (funext fun c => by simp)
    | succ j ih =>
      rw [← ih, ← finrank_W_pow p (fun c => β (b.t i c) ^ p ^ j)]
      exact congrArg (fun ν : 𝓞 D.F → k => Module.finrank k ↥(W ν)) (funext fun c => by rw [_root_.pow_succ, _root_.pow_mul])
  simp only [RingHom.comp_apply, iterateFrobenius_def] at e1 e2
  refine e1.trans (Eq.trans ?_ e2.symm)
  exact congrArg (D.m * D.n * ·) (hW j)
end
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

section
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]
  {A' : Over (Sp (DualNumber k))} [GrpObj A'] {i : A₀.left ⟶ A'.left}

private theorem resMor (h : IsGrpPullback A₀ A' (epsRed k) i) :
    GrpMor (dp0 (DualNumber k)) (𝟙 _) A' (dp0 k) (𝟙 _) A₀ (TrivSqZeroExt.fstHom k k k).toRingHom (epsRed k) i :=
  GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) (by simp; rfl) h

private theorem frob_sq (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0) :
    GlobalTheory.VB.frob A₀.left p (cast_left p k hk A₀) ≫ i = i ≫ GlobalTheory.VB.frob A'.left p (cast_left p _ hT A') :=
  GlobalTheory.VB.frob_naturality p (cast_left p _ hT A') i (cast_left p k hk A₀)

private theorem pow_dual (hk : (p : k) = 0) (r : DualNumber k) :
    r ^ p = algebraMap k (DualNumber k) (TrivSqZeroExt.fst r ^ p) := by
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_pow]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_pow, nsmul_eq_mul, hk]

private theorem res_frob (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (c : primDR A') :
    (resMor h).pull (frobDR p _ hT A' c) = frobDR p k hk A₀ ((resMor h).pull c) := by
  have F' := frobMor p _ hT A' (cast_left p _ hT A')
  have F₀ := frobMor p k hk A₀ (cast_left p k hk A₀)
  have M := F'.comp (resMor h)
  refine (GrpMor.pull_pull F' (resMor h) M (fun _ ↦ rfl) rfl c).trans
    (GrpMor.pull_pull (resMor h) F₀ M (fun r ↦ ?_) (frob_sq hk hT) c).symm
  simp [frobR_apply, TrivSqZeroExt.fst_pow]

private theorem lift_frob (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (c : primDR A') :
    (liftMor (epsDP k) h).pull (frobDR p _ hT A' c) =
      (constMor A₀).pull (frobDR p k hk A₀ ((resMor h).pull c)) := by
  have F' := frobMor p _ hT A' (cast_left p _ hT A')
  have F₀ := frobMor p k hk A₀ (cast_left p k hk A₀)
  have M := F'.comp (liftMor (epsDP k) h)
  have N := (resMor h).comp F₀
  have e₁ := GrpMor.pull_pull F' (liftMor (epsDP k) h) M (fun _ ↦ rfl) rfl c
  have e₂ := GrpMor.pull_pull (resMor h) F₀ N (fun _ ↦ rfl) rfl c
  have e₃ := GrpMor.pull_pull N (constMor A₀) M (fun r ↦ by
    simp [frobR_apply, pow_dual hk r]) (by simpa using frob_sq hk hT) c
  exact e₁.trans (e₃.symm.trans (congrArg _ e₂.symm))

private theorem res_iter (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (n : ℕ) (c : primDR A') :
    (resMor h).pull ((frobDR p _ hT A')^[n] c) = (frobDR p k hk A₀)^[n] ((resMor h).pull c) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', res_frob hk hT h, ih]

private theorem corr_push {x : HdR A₀} {d : Crys (epsDP k) (epsRed k) A₀}
    (hd : (constMor A₀).Corr x d) (u : A₀ ⟶ A₀) [IsMonHom u] (c : primDR A₀) :
    push (epsDP k) (epsRed k) u d ((constMor A₀).pull c) =
      algebraMap k (DualNumber k) (push (dp0 k) (𝟙 _) u x c) :=
  GrpMor.Corr.push (m := constMor A₀) (constMor A₀) u u (by simp) hd c

private theorem vanish (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (hBC : (constMor A₀).IsBC)
    (g₀ : A₀ ⟶ A₀) (g' : A' ⟶ A') [IsMonHom g₀] [IsMonHom g']
    (hg : i ≫ g'.left = g₀.left ≫ i) (n : ℕ) (x : HdR A₀) (d : Crys (epsDP k) (epsRed k) A₀)
    (hd : (constMor A₀).Corr x d)
    (hx : ∀ z, x (primPull (dp0 k) (𝟙 _) g₀ ((frobDR p k hk A₀)^[n + 1] z)) = 0) (c : primDR A') :
    crysToDR (epsDP k) h d (primPull (dp0 (DualNumber k)) (𝟙 _) g' ((frobDR p _ hT A')^[n + 1] c)) = 0 := by
  have e₁ : crysToDR (epsDP k) h d (primPull (dp0 (DualNumber k)) (𝟙 _) g' ((frobDR p _ hT A')^[n + 1] c)) =
      push (epsDP k) (epsRed k) g₀ d ((liftMor (epsDP k) h).pull ((frobDR p _ hT A')^[n + 1] c)) :=
    (LinearMap.congr_fun (crysToDR_push (epsDP k) h h g₀ g' hg d) _).symm
  have e₂ : (liftMor (epsDP k) h).pull ((frobDR p _ hT A')^[n + 1] c) =
      (constMor A₀).pull ((frobDR p k hk A₀)^[n + 1] ((resMor h).pull c)) := by
    rw [Function.iterate_succ_apply', lift_frob hk hT h, res_iter hk hT h,
      Function.iterate_succ_apply']
  rw [e₁, e₂, corr_push hd g₀, push_apply, hx, map_zero]

private theorem dual_zero_of_span {T M : Type*} [CommRing T] [AddCommGroup M] [Module T M] (L : M →ₗ[T] T)
    {S : Set M} (hS : ∀ s ∈ S, L s = 0) {y : M} (hy : y ∈ Submodule.span T S) : L y = 0 :=
  LinearMap.mem_ker.1 ((Submodule.span_le (p := LinearMap.ker L)).2 (fun s hs ↦ LinearMap.mem_ker.2 (hS s hs)) hy)

private theorem alg_eq (a : k) :
    algebraMap k (DualNumber k) a = TrivSqZeroExt.inl a + TrivSqZeroExt.inr 0 := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]


private theorem core (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (hBC : (constMor A₀).IsBC)
    (e₀ g₀ : A₀ ⟶ A₀) (e' g' : A' ⟶ A') [IsMonHom e₀] [IsMonHom g₀] [IsMonHom e'] [IsMonHom g']
    (he : i ≫ e'.left = e₀.left ≫ i) (hg : i ≫ g'.left = g₀.left ≫ i) (f : ℕ) (hf : 0 < f)
    (hNO : NO p (DualNumber k) hT A' e' g' f) (x : HdR A₀)
    (hx : ∀ z, x (primPull (dp0 k) (𝟙 _) g₀ ((frobDR p k hk A₀)^[f] z)) = 0) :
    IsFilLift h (push (dp0 k) (𝟙 _) e₀ x) 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  obtain ⟨d, hd⟩ := hBC.exists x
  refine ⟨push (epsDP k) (epsRed k) e₀ d, ?_, fun c ↦ ?_⟩
  · have hpush := crysToDR_push (epsDP k) h h e₀ e' he d
    change crysToDR (epsDP k) h (push (epsDP k) (epsRed k) e₀ d) ∈ Fil A'
    rw [hpush]
    refine (Submodule.mem_dualAnnihilator _).2 fun y hy ↦ ?_
    have hmem : primPull (dp0 (DualNumber k)) (𝟙 _) e' y ∈ Submodule.span (DualNumber k)
        (Set.range fun c => primPull (dp0 (DualNumber k)) (𝟙 _) g' ((frobDR p (DualNumber k) hT A')^[n + 1] c)) :=
      hNO y hy
    have h0 : crysToDR (epsDP k) h d (primPull (dp0 (DualNumber k)) (𝟙 _) e' y) = 0 :=
      dual_zero_of_span _ (Set.forall_mem_range.2 (vanish hk hT h hBC g₀ g' hg n x d hd hx)) hmem
    exact h0
  · have e₁ := corr_push (x := x) (d := d) hd e₀ c
    exact e₁.trans (alg_eq _)

end

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.estep :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (f : ℕ), 0 < f → ∀ (π : Par p w f)
      (k : Type) [Field k] (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0) (s₀ : Sp k ⟶ Sp R) (s' : Sp (DualNumber k) ⟶ Sp R) (o₀ : Obj b N s₀) (o' : Obj b N s')
      (m : ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), NOo hT o' π →
      ∀ x : HdR o₀.A, (∀ z, x (coh o₀ π.g ((frobDR p k hk o₀.A)^[f] z)) = 0) → IsFilLift m.cart (hom o₀ π.ε x) 0 := by
  intro p _ D R _ b N w f hf π k _ hk hT s₀ s' o₀ o' m hNO x hx
  haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O π.ε)
  haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O π.g)
  haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O π.ε)
  haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O π.g)
  exact core hk hT m.cart (GlobalTheory.HTRealise.isBC_constMor o₀.ab) _ _ _ _ (m.act _).symm (m.act _).symm f hf hNO x hx
end
