import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_4 :
    (List.ofFn coreChunks93_4).flatten =
      (coreData93.take (coreResources93 4).q).drop 17 := by
  decide +kernel

theorem coreCheck93_4 :
    ∀ c : Fin 1, (coreChunks93_4 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 4)) = true := by
  decide +kernel
#print axioms coreFlatten93_4
#print axioms coreCheck93_4
end Erdos883Verified
