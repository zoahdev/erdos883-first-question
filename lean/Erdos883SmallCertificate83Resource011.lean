import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_11 :
    (List.ofFn coreChunks83_11).flatten =
      (coreData83.take (coreResources83 11).q).drop 28 := by
  decide +kernel

theorem coreCheck83_11 :
    ∀ c : Fin 1, (coreChunks83_11 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 11)) = true := by
  decide +kernel
#print axioms coreFlatten83_11
#print axioms coreCheck83_11
end Erdos883Verified
