import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_12 :
    (List.ofFn coreChunks83_12).flatten =
      (coreData83.take (coreResources83 12).q).drop 32 := by
  decide +kernel

theorem coreCheck83_12 :
    ∀ c : Fin 1, (coreChunks83_12 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 12)) = true := by
  decide +kernel
#print axioms coreFlatten83_12
#print axioms coreCheck83_12
end Erdos883Verified
