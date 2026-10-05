import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_15 :
    (List.ofFn coreChunks158_15).flatten =
      (coreData158.take (coreResources158 15).q).drop 32 := by
  decide +kernel

theorem coreCheck158_15 :
    ∀ c : Fin 1, (coreChunks158_15 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 15)) = true := by
  decide +kernel
#print axioms coreFlatten158_15
#print axioms coreCheck158_15
end Erdos883Verified
