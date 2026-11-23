module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamily
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemEig
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LinearIndependentImg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

namespace LevelTowerAlt

theorem exists_isOFamily {E L V : Type} [Field E] [NumberField E] [Field L] [CharZero L] [AddCommGroup V] [Module L V]
    (ρ : 𝓞 E →+* Module.End L V) (I : AddSubgroup V) (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I) {n : ℕ} (e : Fin n → V)
    (he : AddSubgroup.closure (Set.range e) = I) : ∃ (r : ℕ) (v : Fin r → V), IsOFamily ρ I v := by
  letI : Module (𝓞 E) V := Module.compHom V ρ
  have hρ : ∀ (a : 𝓞 E) (x : V), a • x = ρ a x := fun _ _ => rfl
  let N : Submodule (𝓞 E) V := Submodule.span (𝓞 E) (Set.range e)
  let N' : Submodule (𝓞 E) V := { I.toAddSubmonoid with smul_mem' := fun a x hx => hst a x hx }
  have hN : N.toAddSubgroup = I := by
    refine le_antisymm (fun x hx => ?_) ?_
    · have : N ≤ N' := Submodule.span_le.2 fun y hy => by
        change y ∈ I
        rw [← he]
        exact AddSubgroup.subset_closure hy
      exact this hx
    · rw [← he, AddSubgroup.closure_le]
      exact Submodule.subset_span
  haveI : Module.Finite (𝓞 E) N := Module.Finite.span_of_finite _ (Set.finite_range e)
  obtain ⟨y, hy⟩ := exists_linearIndependent_fin (K := E) (E := N)
  have hfin := finite_quotient_span hy (Fintype.card_fin _)
  refine ⟨_, fun i => (y i : V), fun i => ?_, fun a ha => ?_, ?_⟩
  · rw [← hN]
    exact (y i).2
  · funext i
    refine Fintype.linearIndependent_iff.1 hy a (Subtype.ext ?_) i
    simpa [hρ] using ha
  · have h1 : oSpan ρ (fun i => (y i : V)) =
        ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).toAddSubgroup := by
      ext x
      rw [TorPart.mem_oSpan_iff, Submodule.map_span, ← Set.range_comp, Submodule.mem_toAddSubgroup,
        Submodule.mem_span_range_iff_exists_fun]
      exact exists_congr fun c => eq_comm
    have h2 : ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).toAddSubgroup.relIndex N.toAddSubgroup =
        Nat.card (N ⧸ ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).comap N.subtype) := rfl
    rw [h1, ← hN, h2, Submodule.comap_map_eq_of_injective N.injective_subtype]
    exact Nat.card_pos.ne'

theorem exists_append {L V : Type} [Field L] [AddCommGroup V] [Module L V] [Module.Finite L V] {r : ℕ} {w : Fin r → V}
    (hw : LinearIndependent L w) (S : Set V) :
    ∃ (k : ℕ) (q : Fin k → V), (∀ c, q c ∈ S) ∧ LinearIndependent L (Fin.append w q) ∧
      S ⊆ Submodule.span L (Set.range (Fin.append w q)) := by
  set W := Submodule.span L (Set.range w) with hW
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' L (fun x : S => W.mkQ (x : V))
  haveI : Finite κ := hli.finite
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  refine ⟨k, fun c => (a (e.symm c) : V), fun c => (a _).2, ?_, fun x hx => ?_⟩
  · have h1 : LinearIndependent L fun i => (⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩ : W) :=
      LinearIndependent.of_comp W.subtype hw
    have h2 := h1.sumElim_of_quotient (fun c => (a (e.symm c) : V)) (hli.comp e.symm e.symm.injective)
    have h3 := h2.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective
    have h4 : Fin.append w (fun c => (a (e.symm c) : V)) =
        Sum.elim w (fun c => (a (e.symm c) : V)) ∘ finSumFinEquiv.symm := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
    rw [h4]
    exact h3
  · have h1 : W.mkQ x ∈ Submodule.span L (Set.range ((fun x : S => W.mkQ (x : V)) ∘ a)) := by
      rw [hsp]
      exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    have h2 : Set.range ((fun x : S => W.mkQ (x : V)) ∘ a) = W.mkQ '' Set.range fun c => (a (e.symm c) : V) := by
      rw [← Set.range_comp, ← e.symm.surjective.range_comp]
      rfl
    rw [h2, ← Submodule.map_span, ← Submodule.mem_comap, Submodule.comap_map_mkQ] at h1
    rw [range_append, Submodule.span_union]
    exact h1

theorem orthogonal_family_adapted_basis : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A hΨ
  refine ⟨?_, fun r v hv s => ?_⟩
  · obtain ⟨n, e, -, he⟩ := A.I_basis
    exact exists_isOFamily A.ρ A.I A.I_stable e he
  haveI : Module.Finite L V := by
    obtain ⟨S, hS⟩ := A.fg
    refine ⟨S, ?_⟩
    rw [← A.span, ← hS, Submodule.span_span_of_tower]
  obtain ⟨h1, h2, h3, h4⟩ := tor_facts A hΨ hv s
  obtain ⟨k, q, hq, hli, hsp⟩ := exists_append h1 (A.eig s : Set V)
  have had : A.IsAdapted s v fun c => ⟨q c, (hq c).1⟩ := by
    refine ⟨hli, le_antisymm ?_ fun x hx => ?_⟩
    · rw [LinPt.fam, range_append, Submodule.span_le]
      rintro _ (⟨a, rfl⟩ | ⟨c, rfl⟩)
      · exact h2 a
      · exact (hq c).2
    · obtain ⟨c, hc, h5⟩ := exists_smul_mem_eig A s hx
      have hcL : algebraMap (𝓞 L) L c ≠ 0 := by
        rw [map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)]
        exact hc
      have h6 := hsp h5
      rw [← algebraMap_smul L c] at h6
      exact (Submodule.smul_mem_iff _ hcL).1 h6
  obtain ⟨h5, h6⟩ := sub_eig A had.2
  have h7 := relIndex_ne_zero had.1 h5 h6 h5
  rw [LinPt.fam, (index_split A had.1 h3 h4 hq).1] at h7
  have h8 := linearIndependent_img A had.1 h4 hq
  refine ⟨k, _, hq, had, ?_, (rank_img A h8 hq (right_ne_zero_of_mul h7)).1, fun ι => ?_⟩
  · rw [← had.2, finrank_span_eq_card had.1, Fintype.card_fin]
  · rw [gramDet_eq]
    exact gramDet_pos _ _ h8

end LevelTowerAlt
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem LevelTowerAlt.label_degree_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A r k v s q hΨ hv hq had
  obtain ⟨-, -, h3, h4⟩ := LevelTowerAlt.tor_facts A hΨ hv s
  obtain ⟨h5, h6⟩ := LevelTowerAlt.sub_eig A had.2
  have h7 := LevelTowerAlt.relIndex_ne_zero had.1 h5 h6 h5
  obtain ⟨e1, e2⟩ := LevelTowerAlt.index_split A had.1 h3 h4 hq
  rw [LinPt.fam, e1] at h7
  have h8 := (LevelTowerAlt.rank_img A (LevelTowerAlt.linearIndependent_img A had.1 h4 hq) hq (right_ne_zero_of_mul h7)).2
  rw [LinPt.labDeg, HermitianBundle.normDegree, h8, logIdx, logIdx, LinPt.fam, e1, e2, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.2 (left_ne_zero_of_mul h7)) (Nat.cast_ne_zero.2 (right_ne_zero_of_mul h7))]
  ring
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Comparison₂

def LevelFree : Prop :=
  HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type)
    [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ), p ∈ S →
    0 < D.p + D.q → HT.HTFree 𝔐 p → ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q →
      𝔐.M.htOm 𝔐.t.PP.L (p ^ 4) q = 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q

def MuHodge : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (bb : ∀ τ, Fin Dc.N → W τ)
    (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (lam : Ω),
    (∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ)) →
    Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)) →
    ∀ (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z →
    ∃ (h : genPt Or.𝔐.ξ ⤳ centre z) (b : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li)
      (T : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω)
      (Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ),
      (∀ τ, (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)).IsFrameAt (b τ) ⟨centre z, h⟩ ∧ (∀ k, b τ k = ∑ k', T τ k' k • s τ k') ∧
        Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (b τ) (Γ τ) ∧ (Γ τ).PosDef) ∧
      SecNorm Or.𝔐.ξ Dc.y (muVert Hd B)
        (lam⁻¹ * ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p)) z w
        (∏ τ, (T τ).det)⁻¹ (∏ τ, Real.sqrt (Γ τ).det.re)⁻¹

def muExp {Ψ : Type} {N : ℕ} (p : ℕ) (r : Ψ × Fin N) : ℤ := if p ≤ (r.2 : ℕ) then 1 else 0

def Common : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (oR : RootOrigin Y S RM Fx)
    (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ),
    S = S₀ ∪ Dc.SB B → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → oR.𝔐.OmVB → (∀ p ∈ S, oR.𝔐.R p = 4) →
    1 ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt Fx.ξf →
    ∃ (K₃ : Type) (_ : Fintype K₃) (ρ : K₃ → Type) (_ : ∀ k, Fintype (ρ k)) (κ₁ : RM.K → K₃)
      (v₁ : (Σ k, RM.ι k) → Σ k, ρ k) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ρ k) (Ω₃ : Type) (_ : Field Ω₃) (_ : CharZero Ω₃)
      (y : (Σ k, ρ k) → Ω₃) (β : MRing ρ) (d : K₃ → ℕ),
      IsBlockMap κ₁ v₁ ∧ IsBlockMap κ v ∧ mCoordIdeal (y ∘ v₁) = RM.P ∧ mCoordIdeal (y ∘ v) = mCoordIdeal Dc.y ∧
      IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog β d ∧ β ∉ mCoordIdeal y ∧
      IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0 ∧
      (∀ z ∈ mcPts (mCoordIdeal y), evC z β ≠ 0 → (fun p => z (v p)) ∉ Dc.Bd) ∧
      ∀ L L' : HermLine ρ, IsPullHerm κ₁ v₁ (Top.combLine oR.sing (muExp D.p)) L → IsPullHerm κ v (muVert Hd B) L' →
        IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z β ≠ 0} L L'

section Tame

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P B : Ideal (MRing J)} {e : ℕ}

def Tame (R : AnLogRes P B e) (Θ L : LocPot R.X) (s : R.X → R.X → ℂ) (A : ℝ → HermLine J) : Prop :=
  ∃ (ref : HermLine J) (C : ℝ), IsSmoothHerm ref ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (A t) ∧ (A t).a = ref.a ∧
    IsPsh R.A (potOf R (A t) + Θ.rsmul C) ∧ ∀ x ∉ bdry s,
      -C * Real.log (rW L s x) ≤ Real.log ((A t).h (R.lift x x)) - Real.log (ref.h (R.lift x x)) ∧
        Real.log ((A t).h (R.lift x x)) - Real.log (ref.h (R.lift x x)) ≤ C

end Tame

def Replace : Prop :=
  PB.Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (P B : Ideal (MRing J)) (e a b : ℕ) (R : AnLogRes P B e) (Θ L : LocPot R.X) (s : R.X → R.X → ℂ)
    (nb : ℕ) (mb : Fin nb → ℕ) (Wb : Fin nb → Set R.X) (σ : Type) [Fintype σ] (A : ℝ → σ → HermLine J) (M : ℝ → HermLine J)
    (m : σ → ℤ) (n : Fin b → σ → ℤ) (f g : MRing J) (w : ℝ → ((Σ k, J k) → ℂ) → ℝ) (C : ℝ),
    a + b = e + 1 → IsArithVar P (e + 1) → IsPotential R.A Θ → IsPosPot R.A Θ → IsPotential R.A L → IsSection R.A L s →
    IsSNC R.A L s mb Wb → (∀ x, logNormSec L s x ≤ 0) → (∀ i, Tame R Θ L s fun t => A t i) → Tame R Θ L s M →
    (∀ᶠ t in 𝓝[>] (0 : ℝ), IsLineIso P (Top.combLine (A t) m).a (M t).a f g ∧
      IsDefectOn P (mcPts P) f g (Top.combLine (A t) m) (M t) (w t) ∧
      ∀ x ∉ bdry s, |w t (R.lift x x)| ≤ C * Real.log (rW L s x)) →
    (∀ K' ⊆ (bdry s)ᶜ, IsCompact K' → TendstoUniformlyOn (fun t x => w t (R.lift x x)) (fun _ => 0) (𝓝[>] 0) K') →
    Tendsto (fun t => II K J P (a + b) (Fin.append (fun _ : Fin a => M t) fun j => Top.combLine (A t) (n j)) -
      II K J P (a + b) (Fin.append (fun _ : Fin a => Top.combLine (A t) m) fun j => Top.combLine (A t) (n j)))
      (𝓝[>] 0) (𝓝 0)

def RegUnif : Prop :=
  ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n : ℕ) (M : CxModel P n)
    (Xo : Set ((Σ k, J k) → ℂ)) (A : HermLine J) (S : LogLogRegularisationSetting M Xo A) (V : Set M.Xc) (g : M.Xc → ℝ), S.IsTied →
    IsOpen V → ContinuousOn g V → (∀ x ∈ V ∩ S.R.Yo, g x = S.R.ph x) →
    (∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ x, S.regWeight t x ≤ C) ∧ ∀ x ∈ V, g x ≤ S.regWeight t x) ∧
      ∀ K' ⊆ V, IsCompact K' → TendstoUniformlyOn S.regWeight g (𝓝[>] 0) K'

def BaseSide : Prop :=
  ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type)
    [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W)
    (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (K' : Type) [Fintype K'] (J' : K' → Type)
    [∀ k, Fintype (J' k)] (P' B' : Ideal (MRing J')) (e : ℕ) (R : AnLogRes P' B' e) (κ : K → K') (v : (Σ k, J k) → Σ k, J' k)
    (Θ : LocPot R.X) (Mt : ℝ → HermLine J'), S.IsTied → IsBlockMap κ v → imageZ v P' = mCoordIdeal D.y →
    IsPotential R.A Θ → IsPosPot R.A Θ → (∀ t, IsPullHerm κ v (muReg Hd S B t) (Mt t)) →
    ∃ (ref : HermLine J') (C : ℝ), IsSmoothHerm ref ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (Mt t) ∧ (Mt t).a = ref.a ∧ IsPsh R.A (potOf R (Mt t) + Θ.rsmul C) ∧
        (∀ x, Real.log ((Mt t).h (R.lift x x)) - Real.log (ref.h (R.lift x x)) ≤ C) ∧
        ∀ x, (fun p => R.lift x x (v p)) ∉ D.Bd →
          Real.log ((muVert Hd B).h fun p => R.lift x x (v p)) ≤ Real.log ((Mt t).h (R.lift x x))) ∧
      ∀ K₀ ⊆ {x | (fun p => R.lift x x (v p)) ∉ D.Bd}, IsCompact K₀ → TendstoUniformlyOn
        (fun t x => Real.log ((Mt t).h (R.lift x x)) - Real.log ((muVert Hd B).h fun p => R.lift x x (v p)))
        (fun _ => 0) (𝓝[>] 0) K₀

end LevelTowerAlt.Comparison₂
end
end
