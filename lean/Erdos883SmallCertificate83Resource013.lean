import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_13 :
    (List.ofFn coreChunks83_13).flatten =
      (coreData83.take (coreResources83 13).q).drop 33 := by
  decide +kernel

theorem coreCheck83_13 :
    ∀ c : Fin 1, (coreChunks83_13 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 13)) = true := by
  decide +kernel
#print axioms coreFlatten83_13
#print axioms coreCheck83_13
end Erdos883Verified
