import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_21 :
    (List.ofFn coreChunks158_21).flatten =
      (coreData158.take (coreResources158 21).q).drop 40 := by
  decide +kernel

theorem coreCheck158_21 :
    ∀ c : Fin 1, (coreChunks158_21 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 21)) = true := by
  decide +kernel
#print axioms coreFlatten158_21
#print axioms coreCheck158_21
end Erdos883Verified
