import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_6 :
    (List.ofFn coreChunks93_6).flatten =
      (coreData93.take (coreResources93 6).q).drop 20 := by
  decide +kernel

theorem coreCheck93_6 :
    ∀ c : Fin 1, (coreChunks93_6 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 6)) = true := by
  decide +kernel
#print axioms coreFlatten93_6
#print axioms coreCheck93_6
end Erdos883Verified
