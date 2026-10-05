import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_25 :
    (List.ofFn coreChunks158_25).flatten =
      (coreData158.take (coreResources158 25).q).drop 49 := by
  decide +kernel

theorem coreCheck158_25 :
    ∀ c : Fin 1, (coreChunks158_25 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 25)) = true := by
  decide +kernel
#print axioms coreFlatten158_25
#print axioms coreCheck158_25
end Erdos883Verified
