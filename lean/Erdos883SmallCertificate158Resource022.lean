import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_22 :
    (List.ofFn coreChunks158_22).flatten =
      (coreData158.take (coreResources158 22).q).drop 44 := by
  decide +kernel

theorem coreCheck158_22 :
    ∀ c : Fin 1, (coreChunks158_22 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 22)) = true := by
  decide +kernel
#print axioms coreFlatten158_22
#print axioms coreCheck158_22
end Erdos883Verified
