import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_35 :
    (List.ofFn coreChunks158_35).flatten =
      (coreData158.take (coreResources158 35).q).drop 43 := by
  decide +kernel

theorem coreCheck158_35 :
    ∀ c : Fin 1, (coreChunks158_35 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 35)) = true := by
  decide +kernel
#print axioms coreFlatten158_35
#print axioms coreCheck158_35
end Erdos883Verified
