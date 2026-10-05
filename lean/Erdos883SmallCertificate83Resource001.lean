import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_1 :
    (List.ofFn coreChunks83_1).flatten =
      (coreData83.take (coreResources83 1).q).drop 0 := by
  decide +kernel

theorem coreCheck83_1 :
    ∀ c : Fin 1, (coreChunks83_1 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 1)) = true := by
  decide +kernel
#print axioms coreFlatten83_1
#print axioms coreCheck83_1
end Erdos883Verified
