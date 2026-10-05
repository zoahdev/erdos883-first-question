import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_28 :
    (List.ofFn coreChunks158_28).flatten =
      (coreData158.take (coreResources158 28).q).drop 61 := by
  decide +kernel

theorem coreCheck158_28 :
    ∀ c : Fin 1, (coreChunks158_28 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 28)) = true := by
  decide +kernel
#print axioms coreFlatten158_28
#print axioms coreCheck158_28
end Erdos883Verified
