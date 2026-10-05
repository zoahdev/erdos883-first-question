import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_14 :
    (List.ofFn coreChunks83_14).flatten =
      (coreData83.take (coreResources83 14).q).drop 0 := by
  decide +kernel

theorem coreCheck83_14 :
    ∀ c : Fin 2, (coreChunks83_14 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 14)) = true := by
  decide +kernel
#print axioms coreFlatten83_14
#print axioms coreCheck83_14
end Erdos883Verified
