import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_10 :
    (List.ofFn coreChunks158_10).flatten =
      (coreData158.take (coreResources158 10).q).drop 27 := by
  decide +kernel

theorem coreCheck158_10 :
    ∀ c : Fin 1, (coreChunks158_10 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 10)) = true := by
  decide +kernel
#print axioms coreFlatten158_10
#print axioms coreCheck158_10
end Erdos883Verified
