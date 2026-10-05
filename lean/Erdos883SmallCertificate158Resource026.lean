import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_26 :
    (List.ofFn coreChunks158_26).flatten =
      (coreData158.take (coreResources158 26).q).drop 53 := by
  decide +kernel

theorem coreCheck158_26 :
    ∀ c : Fin 1, (coreChunks158_26 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 26)) = true := by
  decide +kernel
#print axioms coreFlatten158_26
#print axioms coreCheck158_26
end Erdos883Verified
