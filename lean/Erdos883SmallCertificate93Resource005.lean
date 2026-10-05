import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_5 :
    (List.ofFn coreChunks93_5).flatten =
      (coreData93.take (coreResources93 5).q).drop 19 := by
  decide +kernel

theorem coreCheck93_5 :
    ∀ c : Fin 1, (coreChunks93_5 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 5)) = true := by
  decide +kernel
#print axioms coreFlatten93_5
#print axioms coreCheck93_5
end Erdos883Verified
