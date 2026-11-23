module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.EigChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.MemOrdC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle008
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ProjectiveTransportAlongEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta

@[expose] public section

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem up_list {σ : Type} [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (g : ∀ v, G v) (w : σ) (s : List σ)
    (hs : s.Nodup) : (s.map fun v => Pi.mulSingle v (g v)).prod w = if w ∈ s then g w else 1 := by
  induction s with
  | nil => simp
  | cons v s ih =>
    rw [List.nodup_cons] at hs
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hs.2]
    by_cases h : w = v
    · subst h; simp [hs.1]
    · simp [h]
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ)
private theorem up_VV (d : ℕ) (v v' : H.V) (h : v ≠ v') (g g') (F) :
    H.atV d v g (H.atV d v' g' F) = H.atV d v' g' (H.atV d v g F) := by
  classical
  change (H.X.rpF ℂ d H.m (Pi.mulSingle v g) * H.X.rpF ℂ d H.m (Pi.mulSingle v' g')) F =
    (H.X.rpF ℂ d H.m (Pi.mulSingle v' g') * H.X.rpF ℂ d H.m (Pi.mulSingle v g)) F
  rw [← map_mul, ← map_mul, (Pi.mulSingle_commute (f := fun v : H.V => GLw n (H.Sl v)) h g g').eq]
private theorem up_PA (d : ℕ) (g u) (F) :
    H.X.rpF ℂ d H.m g (H.X.raF d (H.τC ι) u F) = H.X.raF d (H.τC ι) u (H.X.rpF ℂ d H.m g F) := by
  funext i x k
  change (H.X.ra (H.τC ι) u (fun y j => F j y k) (x * (1, g))) i =
    H.X.ra (H.τC ι) u (fun y j => F j (y * (1, g)) k) x i
  rw [Frame.ra_apply, Frame.ra_apply]
  simp [mul_assoc]
private theorem up_vec (hL : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hH : H.Ax) {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ}
    (Y : H.PartAltAlt ι lam ξ) (K : H.Lev) (hK : ∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (hω : ∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) (e : ℕ)
    (he : ∀ v i, ∀ y ∈ Uc _ (e + 1), ω v i y = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v)) :
    ∃ F ∈ Y.Y, F ≠ 0 ∧ (∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) ∧
      ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q) := by
  refine Exists.imp (fun F h => ⟨h.1, h.2.1, fun v => h.2.2 (.inl v), fun q => h.2.2 (.inr q)⟩) (Up.meet (I := H.V ⊕ H.Q)
    (Sum.elim (fun v => Set.range (H.atV d v)) fun q => Set.range (H.atW ι d (H.wq q)))
    (Sum.elim (fun v => Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) fun q => fixd (H.atW ι d (H.wq q)) (K.1 q))
    Y.Y Y.ne ?_ ?_ ?_)
  · rintro (v | q) _ ⟨g, rfl⟩
    · exact Up.isoStab (Y.isoL v) g
    · exact Up.isoStab (Y.isoQ q) g
  · rintro (v | q) (v' | q') hne _ ⟨g, rfl⟩
    · exact Up.ordMap _ _ _ (fun g' F => up_VV H d v' v (fun h => hne (by rw [h])) g g' F) _ _ _
    · exact Up.ordMap _ _ _ (fun g' F => (up_PA H ι d _ _ F).symm) _ _ _
    · exact Up.fixMap (H.atW ι d (H.wq q)) (H.atW ι d (H.wq q)) _ (fun g' F => up_PA H ι d _ _ F) _
    · refine Up.fixMap _ _ _ (fun g' F => ?_) _
      change (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F = (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F
      rw [← map_mul, ← map_mul]
      exact congrArg (fun u => H.X.raF d (H.τC ι) u F) (hH.Q_Q q q' (fun h => hne (by rw [h])) g' g).eq.symm
  · rintro (v | q) Z hZ hne hst
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoL v) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2, hu3⟩ := _root_.UpperTheory.V.Hi.exists_ne_zero_mem_eig_uOp_eq_psEig_smul_of_equiv_ps hL _ n _ (Y.σl v).ρ (ω v) (hω v) e (he v) (φ v) (hφ v)
      refine (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, ?_⟩, fun h => hu2 (hp3 (by rw [h, map_zero]))⟩
      exact Up.ordMap _ _ p hp1 _ _ _ u ((Up.mem_ordC _ _ _ _ _).2 ⟨hu1, hu3⟩)
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoQ q) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2⟩ := (Submodule.ne_bot_iff _).1 (hK q)
      exact (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, Up.fixMap _ _ p hp1 _ u hu1⟩,
        fun h => hu2 (hp3 (by rw [h, map_zero]))⟩
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem up_ord {A : Type} [CommRing A] (θ : H.X.I.T →* Aˣ) (x : A →+* Qbar l)
    {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ} (K : H.Lev)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (e : ℕ)
    (hω : ∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x lam v i u) = 1)
    (hn : ∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v))
    (F : Fin H.m → H.X.Fn ℂ d) (hB : F ∈ H.Big ι ξ) (hV : ∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v)))
    (hQ : ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q)) :
    F ∈ H.OrdAt θ ι x lam ξ K e ∧ ∀ v (j : Fin n),
      H.opC ι lam d (.inr (v, j)) F = ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) • F := by
  classical
  simp only [Up.mem_ordC] at hV
  let I := fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n
  have hN : F ∈ fixd (H.X.rpF ℂ d H.m) H.X.I.N := Up.fixPi _ (fun v => (I v).N) F fun v => (hV v).1.1
  have hNm : F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.Nm e) := Up.fixPi _ (fun v => (I v).Nm e) F fun v => (hV v).1.2.1
  have hlev : F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K) := by
    intro u hu
    let St : Subgroup H.X.Ub :=
      (MulAction.stabilizer (Module.End ℂ (Fin H.m → H.X.Fn ℂ d))ˣ F).comap (H.X.raF d (H.τC ι)).toHomUnits
    have : H.lev K ≤ St := sup_le (fun u hu => hB.2 u hu) (iSup_le fun q => by
      rintro _ ⟨g, hg, rfl⟩
      exact hQ q g hg)
    exact this hu
  have hCl : F ∈ H.ClAt θ ι x lam ξ K e := by
    refine ⟨⟨⟨⟨hB, hlev⟩, hN⟩, hNm⟩, ?_⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro v i y
    have h1 := (hV v).1.2.2 (eT _ n i y)
    rw [hφ v i y, inv_inv, eq_inv_of_mul_eq_one_left (hω v i y)] at h1
    exact h1
  have hz : ∀ v, (I v).uOp (H.atV d v) (I v).z F = ((List.range n).map (psEig (ω v))).prod • F := by
    intro v
    have h1 := (glBridge ((H.Sl v).adicCompletion L) n _ (H.atV d v)).2.2.2.2.2.2.2.2.1
    have h2 := (Up.uOpList (I v) (H.atV d v) F (hV v).1.1 (al _ n) (psEig (ω v)) (List.range n)
      fun j hj => ⟨al_mem _ n j, (hV v).2 j (List.mem_range.1 hj).le⟩).2
    rwa [← h1] at h2
  have hZ := (Up.uOpList (piIwa I) (H.X.rpF ℂ d H.m) F hN (fun v => Pi.mulSingle v (I v).z)
    (fun v => ((List.range n).map (psEig (ω v))).prod) Finset.univ.toList
    fun v _ => ⟨Up.singleP I v _ (I v).z_mem, (Up.uOpPi I _ v _ (I v).z_mem F hN).trans (hz v)⟩).2
  have hzz : (Finset.univ.toList.map fun v => (Pi.mulSingle v (I v).z : GV n H.Sl)).prod = H.X.I.z := by
    funext w
    rw [up_list (fun v => (I v).z) w _ (Finset.nodup_toList _), if_pos (by simp)]
    rfl
  rw [hzz, Finset.prod_map_toList] at hZ
  have hl : ∀ v, ((List.range n).map (psEig (ω v))).prod = ∏ j ∈ Finset.range n, psEig (ω v) j := fun v => rfl
  simp only [hl] at hZ
  refine ⟨?_, fun v j => ?_⟩
  · refine Submodule.mem_iSup_of_mem
      ⟨∏ v, ∏ j ∈ Finset.range n, (H.lowVal ι lam v j)⁻¹ * psEig (ω v) j, ?_⟩ ⟨hCl, ?_⟩
    · rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun j hj => ?_
      rcases j with _ | j
      · simp [HSet.lowVal, psEig]
      · exact hn v ⟨j, by have := Finset.mem_range.1 hj; omega⟩
    · refine Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 ?_)
      change (∏ v, ∏ j ∈ Finset.range n, H.lowVal ι lam v j)⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) H.X.I.z F = _
      rw [hZ, smul_smul]
      simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  · change (H.lowVal ι lam v (j + 1))⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) (Pi.mulSingle v (al _ n (j + 1))) F = _
    rw [Up.uOpPi I _ v _ (al_mem _ n _) F hN, ← smul_smul]
    exact congrArg _ ((hV v).2 _ j.2)
end
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Hi.coreUp_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (Y : H.PartAltAlt ι lam ξ) (K : H.Lev), (∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥) → ∀ ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, (∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) → (∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x.toRingHom lam v i u) = 1) → ∀ a : H.Op → c.O, (∀ w (j : Fin n), ‖ι.symm (Y.a w (j + 1)) - algebraMap c.O (Qbar l) (a (.inl (w, j)))‖ < 1) → (∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1 ∧ ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) - algebraMap c.O (Qbar l) (a (.inr (v, j)))‖ < 1) → ∀ [Fact (CommOn (H.MK θ a K) (H.op A))], H.MK θ a K ≠ ⊥ ∧ ∃ y : H.TK θ a K →ₐ[c.O] Qbar l, y.toRingHom.comp (algebraMap A _) = x.toRingHom ∧ (∀ w (j : Fin n), ι (y (H.gen θ a K (.inl (w, j)))) = Y.a w (j + 1)) ∧ ∀ v (j : Fin n), ι (y (H.gen θ a K (.inr (v, j)))) = (H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1) := by
  intro hL L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K hK ω hω1 hω2 a ha1 ha2 hFact
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hC, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  choose φ hφ using fun v => Up.exInv (ω v)
  obtain ⟨F, hF, h0, hV, hQ⟩ := up_vec H ι hL hH Y K hK ω hω1 c0 (fun v i y hy => by
    have h := hω2 v i ⟨y, Up.Uc_le _ hy⟩
    rw [hsp.triv v i _ hy, map_one, mul_one] at h
    exact Units.ext h) φ hφ
  obtain ⟨hO, hU⟩ := up_ord H ι θ x.toRingHom K ω c0 hω2 (fun v j => (ha2 v j).1) φ hφ F (Y.le hF) hV hQ
  rw [← hsp.span K c0 le_rfl] at hO
  have hx2 : ∀ b ∈ maximalIdeal A, ‖x.toRingHom b‖ < 1 := Up.normLt x
  have hx1 : ∀ b, ‖x.toRingHom b‖ ≤ 1 := by
    intro b
    obtain ⟨o, ho⟩ := Alg.IsCO.res_surj (O := c.O) b
    have h1 : ‖x (algebraMap c.O A o)‖ ≤ 1 := by
      rw [x.commutes]
      exact (Up.intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) o).map c.O.val)
    have h2 : x.toRingHom b = x.toRingHom (b - algebraMap c.O A o) + x (algebraMap c.O A o) := by simp
    rw [h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx2 _ ho).le h1)
  haveI : Fact (CommOn (locPart (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) fun i => algebraMap c.O A (a i)) (H.op A)) := hFact
  obtain ⟨hne, y, hy1, hy2⟩ := Up.eigPt (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) hC ι x.toRingHom hx1 hx2 sp
    (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K) F hO h0
    (Sum.elim (fun p => Y.a p.1 (p.2 + 1)) fun p => (H.lowVal ι lam p.1 (p.2 + 1))⁻¹ * psEig (ω p.1) (p.2 + 1))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact Y.sph w _ F hF
      · exact hU v j)
    (fun i => algebraMap c.O A (a i))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact (x.commutes _).symm ▸ ha1 w j
      · exact (x.commutes _).symm ▸ (ha2 v j).2)
  refine ⟨hne, ⟨y, fun o => ?_⟩, RingHom.ext hy1, fun w j => hy2 (.inl (w, j)),
    fun v j => hy2 (.inr (v, j))⟩
  refine Eq.trans (congrArg y ?_) ((hy1 _).trans (x.commutes o))
  exact Subtype.ext (LinearMap.ext fun f => (algebraMap_smul A o f).symm)
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.projectedFormsSystemPart
open UpperTheory.V.Z.Ord UpperTheory.Zero.LLC
def PartLinkAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ)
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ → ∀ (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → YOf Q ι τ₀ e ξ σ ≠ ⊥ →
    ∃ Y : (hset Q τ₀).PartAltAlt ι lam ξ, Y.Y = YOf Q ι τ₀ e ξ σ ∧ (Af.IsIrr (Y.r.comp V.pr) →
      ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (Y.r.comp V.pr) π ∧
        (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧
        ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), π.IsLocComp w τ →
          IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ)
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
end UpperTheory.Gal.projectedFormsSystemPart
end
end
end

section




section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
theorem jacProd_of_alt (hjF : G.Step_jacFin_alt) (hsub : G.SubquotientProp) (hten : G.Step_tensor_alt) (hsupp : G.Step_suppProd_alt) :
    G.Step_jacProd_alt := by
  intro L V _ _ π hs hirr hy
  obtain ⟨hsm, hfl⟩ := hjF L V π hs hirr
  obtain ⟨X, _, _, σ, hσs, hσi, hsq, hση⟩ := hsub _ (jacU G.e π) hsm hfl hy
  obtain ⟨Y, _, _, τ, hτs, hτi, hτd, ⟨eqv⟩⟩ := hten L X σ hσs hσi hση
  refine hsupp L V π hs hirr Y τ hτs hτi hτd ?_
  obtain ⟨S, f, hf⟩ := hsq
  exact ⟨S, (eqv.toIntertwiningMap).comp f, eqv.toLinearEquiv.surjective.comp hf⟩
end Grp
def CStepsAlt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Grp.CompactConductorBasicProp (k := k) ∧ Grp.UniformizerProp (k := k) ∧ Grp.ExistsGroupElementProp (k := k) ∧ ∀ (n : ℕ) (G : Grp k n),
    G.CompactConductorBoundProp ∧ G.JacquetOneProp ∧ G.JacquetMultiplicativeProp ∧ G.JacquetInverseProp ∧ G.CompactOpenKernelProp ∧ G.ModulusOnUnitsProp ∧ G.ModulusMultiplicativeProp ∧
    G.LambdaMultiplicativeProp ∧ G.LambdaBasicProp ∧ G.LambdaUnipotentProp ∧ G.IwahoriDecompositionProp ∧ G.FixedSubspaceStableProp ∧ G.FixedSubspaceFiniteProp ∧ G.NonzeroLeviEigenvectorExists ∧
    G.ParabolicJacquetProp ∧ G.AnnihilationProp ∧ G.NonIntegralProp ∧ G.TorusCentreEigenProp ∧ G.TorusPowerProp ∧ G.JacquetKernelProp ∧ G.TorusCentreInjectiveProp ∧
    G.JacquetImageProp ∧ G.Step_jacFin_alt ∧ G.SubquotientProp ∧ G.Step_tensor_alt ∧ G.Step_suppProd_alt
open UpperTheory.NonzeroTypeTheory in
theorem twisted_spherical_product_of_irreducible_of_eigenvector (hC : _root_.UpperTheory.TNZ.CStepsAlt) (hlL : LeviSubgroupRestriction) (L : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ := by
  intro k _ _ _ _ n G V _ _ ρ hs hi hx
  obtain ⟨hcb, hun, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, hlU, hiw, -, -, -, hPJ, hkill, hni, hTE, hTp, hjK, hTI,
    hjI, hjF, hsub, hten, hsupp⟩ := hG n G
  exact G.cMain_alt hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp hjK hTI hun hlL hjI
    (G.jacProd_of_alt hjF hsub hten hsupp) L V ρ hs hi hx
open UpperTheory.NonzeroTypeTheory in
theorem need_CProps_alt (hC : _root_.UpperTheory.TNZ.CStepsAlt) : Need_CProps := by
  intro k _ _ _ _ n G
  obtain ⟨hcb, -, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, -, -, hV0s, hV0f, hv0, -⟩ := hG n G
  have hK := hKC hccB G.lev
  have hlB' := hlB hccB
  have hlM' := hlM hcb hΔU hΔM hccB
  obtain ⟨h1, h2, h3⟩ := hv0 hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  refine ⟨fun g hg => hg.1, hJone.1, fun g hg g' hg' => ⟨hJmul hcb hccB g hg g' hg', hlM' g hg g' hg'⟩, hJinv hcb hccB,
    fun g _ => hlB'.2.1 g, hK.2.2.1, ?_, hK.2.2.2.2 le_rfl, hlB'.2.2, fun φ hφ k' => hV0s hccB hKC k' φ hφ, hV0f hccB hKC, h1, h2, h3⟩
  rw [← hK.1]
  exact (KCg k n G.lev).one_mem
open UpperTheory.NonzeroTypeTheory in
theorem need_Grp_alt (hC : _root_.UpperTheory.TNZ.CStepsAlt) : Need_Grp := by
  intro k _ _ _ _ n μ hμ
  obtain ⟨-, -, hex, -⟩ := hC k
  obtain ⟨G, σ, h⟩ := hex n μ hμ
  exact ⟨G, σ, fun i => (h i).symm⟩
end UpperTheory.TNZ
end
end
end

section




section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut
namespace UpperTheory.V.UnitaryThreeInertia
def HostRigid_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∀ (ι : Qbar l ≃+* ℂ) (g₁ : Gam Ω S), F.Marked g₁ → ∀ r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l), F.IsCharZeroPt g₁ r →
    (_root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat) → F.Rigid r
def HostNumber_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K → ∃ C : ℕ,
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∀ (ι : Qbar l ≃+* ℂ) (g₁ : Gam Ω S), F.Marked g₁ → ∃ φ : Gam Ω S,
    (∀ r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l), F.IsCharZeroPt g₁ r → TypeI F.η r → (_root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat) →
      (r φ).mat.trace ≠ (F.rz (PadicAlgCl l) φ).mat.trace) ∧
    ∀ (n : ℕ) (r : Fin n → (Gam Ω S →* GG (m := 3) (R := PadicAlgCl l))),
      (∀ i, F.IsCharZeroPt g₁ (r i) ∧ TypeI F.η (r i) ∧ _root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r i (toGS Ω _ s)).mat) →
      (∀ i i', MatIso F.η.ker (mats (r i)) (mats (r i')) → i = i') →
      (∑ i, vl1 l ((r i φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace)) * Real.log l ≤ ((l : ℝ) * N * e) ^ C
end UpperTheory.V.UnitaryThreeInertia
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
variable {l : ℕ} {x δ : kˣ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}
  {P T : Matrix (Fin n) (Fin n) ℂ}
end Loc
def LocDataTAlt : Prop :=
  _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ fr τ : G E Ω, fr ∈ Dec (F := E) Bq → IsFrob (F := E) Bq (normV w) fr⁻¹ → GlobalTheory.TameQuot.IsProGen E Bq l τ → resCard (w.adicCompletion E) = normV w ∧ ∃ x δ : (w.adicCompletion E)ˣ, IsUnif x ∧ IsGenMod _ (ellC l _) δ ∧ ∀ (n : ℕ) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), (∀ rc : IrrGL (k := w.adicCompletion E) → WD hB, IsRecT hB rc → WDT ι r (rc (algNorm σ))) → LocRelT l x δ σ.ρ ((r fr : Matrix (Fin n) (Fin n) (Qbar l)).map ι) ((r τ : Matrix (Fin n) (Fin n) (Qbar l)).map ι)
end UpperTheory.V.Z.Win
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Pa.Lev
section Th
variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
end Th
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r} {J : Ideal B.B} {D : ℕ} {b : TWBase (pairOf B.u) J Empty D}
  {V : s.Lev} {h : (globOf r V).Hom (globOf r V0)} {q : ℕ} {w : Fin q → Plc L}
def LocalLevelConditions (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ) (ph ta : Fin q → (globOf r V).G₀) : Prop :=
  ∃ ι : Qbar l ≃+* ℂ, (∀ m : A.P, (∀ y : _root_.UpperTheory.V.Pa.LevPtAlt A ι, y.sp m = 0) → m = 0) ∧ ∀ (y : _root_.UpperTheory.V.Pa.LevPtAlt A ι) j,
    _root_.UpperTheory.V.Z.Win.LocRelT l (x j) (δ j) (y.σ j).ρ ((mat y.rep (ph j)).map ι) ((mat y.rep (ta j)).map ι)
end UpperTheory.V.Pa.Lev
end
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.V.Hi.module_structure_of_commuting {A R P G : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Group G]
    (ρ : Representation A G P) (α : R →+* Module.End A P) (hc : ∀ t g z, α t (ρ g z) = ρ g (α t z)) :
    ∃ (_ : Module R P) (ρR : Representation R G P), (∀ (t : R) (z : P), t • z = α t z) ∧ ∀ g z, ρR g z = ρ g z := by
  letI : Module R P := Module.compHom P α
  have hs : ∀ (t : R) (z : P), t • z = α t z := fun _ _ => rfl
  refine ⟨inferInstance,
    { toFun := fun g =>
        { toFun := fun z => ρ g z
          map_add' := fun x y => map_add _ x y
          map_smul' := fun t z => by rw [hs, RingHom.id_apply, hs, hc] }
      map_one' := by ext z; simp
      map_mul' := fun g h => by ext z; simp }, hs, fun _ _ => rfl⟩
theorem UpperTheory.V.Hi.levelUR2ModPack_alt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V₀ : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V₀.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : Pa.TWBase (Pa.pairOf B.u) J Empty D) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V₀)) (q : ℕ) (w : Fin q → Plc L) (rN : Resid (Pa.globOf r V).frame O n), Pa.Glob.Compat h rN (Pa.residOf r) → ∀ (R : Type) [CommRing R] [Algebra O R] [Alg.IsCO O R] (p : Pair rN R) (A : Type) [CommRing A] [Algebra O A] (e : Pa.abelian₂ O Empty D ≃ₐ[O] A) (lam : A →ₐ[O] R), (∀ k, lam (e (MvPowerSeries.X (.inr k))) = algebraMap O R (b.wt.c k) * (p.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : R) - 1) → ∀ β : R →ₐ[O] B.B, p.Maps β.toRingHom ((Pa.pairOf B.u).D.comap h.p₀) (Pa.pairOf B.u).ψ → ∀ (P : Type) [AddCommGroup P] [Module A P] (ρ : Representation A (GV n w) P) (α : R →+* Module.End A P), (∀ a z, α (lam a) z = a • z) → (∀ t g z, α t (ρ g z) = ρ g (α t z)) → Module.Finite A (fixd ρ (Pa.UIw1 l n w)) → ∀ [((Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)).Normal] (ρ' : Representation A (Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)) (fixd ρ (Pa.UIw1 l n w))), (∀ (u : Pa.UIw n w) f, (ρ' (u : Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)) f).1 = ρ u f) → Module.Projective (MonoidAlgebra A (Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w))) ρ'.asModule → ∀ eM : fixd ρ (Pa.UK n w) ≃+ b.M, (∀ (t : R) (m m' : fixd ρ (Pa.UK n w)), (m' : P) = α t m → eM m' = β t • eM m) → ∀ ι : Qbar l ≃+* ℂ, (∀ z : P, z ≠ 0 → ∃ (x : R →+* Qbar l) (ρx : (Pa.globOf r V).G₀ →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n w) Y) (sp : P →+ Y) (σ : ∀ j, SmIrr (GLw n (w j))), sp z ≠ 0 ∧ Continuous ρx ∧ p.D.map x = W.GDet.ofRep (W.mat ρx) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ j, IsoSum (π.comp (Pa.atJ n w j)) ⊤ (σ j)) ∧ ∀ j (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (w j)) (rc : IrrGL (k := (w j).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc → _root_.UpperTheory.V.Z.Win.WOT ι (ρx.comp V.pr) (rc (algNorm (σ j)))) → ∃ M : Pa.LevMod b h w, M.ClassicalAlt := by
  intro l _ L Ω _ _ _ _ _ _ s V₀ O _ _ _ n r B J D b V h q w rN hcomp R _ _ _ p A _ _ e lam hlam β hβ P _ _ ρ α hα hc hfin
    hN ρ' hρ' hproj eM heM ι hcl
  obtain ⟨modR, ρR, hs, hρR⟩ := UpperTheory.V.Hi.module_structure_of_commuting ρ α hc
  letI algL : Algebra (Pa.abelian₂ O Empty D) R := (lam.toRingHom.comp e.toRingEquiv.toRingHom).toAlgebra
  have halg : ∀ a : Pa.abelian₂ O Empty D, algebraMap (Pa.abelian₂ O Empty D) R a = lam (e a) := fun _ => rfl
  haveI towO : IsScalarTower O (Pa.abelian₂ O Empty D) R := IsScalarTower.of_algebraMap_eq fun x => by
    rw [halg, e.commutes, lam.commutes]
  letI modL : Module (Pa.abelian₂ O Empty D) P := Module.compHom P e.toRingEquiv.toRingHom
  have hL : ∀ (a : Pa.abelian₂ O Empty D) (z : P), a • z = e.toRingEquiv a • z := fun _ _ => rfl
  haveI tow : IsScalarTower (Pa.abelian₂ O Empty D) R P := ⟨fun a t z => by
    rw [Algebra.smul_def, halg, mul_smul, hs, hα, hL]; rfl⟩
  obtain ⟨hF, hP⟩ := UpperTheory.V.Hi.levelUR2ProjTr (Pa.abelian₂ O Empty D) A R P (GV n w) e.toRingEquiv hL ρ ρR hρR
    (Pa.UIw n w) (Pa.UIw1 l n w)
  obtain ⟨ρ'', h1, h2⟩ := hP ρ' hρ' hproj
  have hmem : ∀ z : P, z ∈ fixd ρR (Pa.UK n w) ↔ z ∈ fixd ρ (Pa.UK n w) := fun z =>
    forall_congr' fun u => forall_congr' fun _ => by rw [hρR]
  let φ : fixd ρR (Pa.UK n w) ≃+ fixd ρ (Pa.UK n w) :=
    { toFun := fun v => ⟨v.1, (hmem _).1 v.2⟩
      invFun := fun v => ⟨v.1, (hmem _).2 v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let M : Pa.LevMod b h w :=
    { rN := rN
      compat := hcomp
      R := R
      p := p
      segmentWeightExponent := fun k => (halg _).trans (hlam k)
      β := β
      β_pair := hβ
      P := P
      ρ := ρR
      fin := hF hfin
      proj := ⟨hN, ρ'', h1, h2⟩
      eM := φ.trans eM
      eM_smul := fun t m => heM t (φ m) (φ (t • m)) (hs t m.1) }
  refine ⟨M, ι, fun m hm => ?_⟩
  by_contra h0
  obtain ⟨x, ρx, Y, iY, mY, π, sp, σ, hne, hcont, hdet, hsm, hact, hiso, hlg⟩ := hcl m h0
  exact hne (hm
    { θ := x
      rep := ρx
      cont := hcont
      det := hdet
      Y := Y
      π := π
      sp := sp
      sp_smul := fun t y => (congrArg sp (hs t y)).trans (hsm t y)
      sp_act := fun g y => (congrArg sp (hρR g y)).trans (hact g y)
      σ := σ
      iso := hiso
      lg := hlg })
end
end
