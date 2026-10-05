import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_6 :
    (List.ofFn coreChunks83_6).flatten =
      (coreData83.take (coreResources83 6).q).drop 19 := by
  decide +kernel

theorem coreCheck83_6 :
    ∀ c : Fin 1, (coreChunks83_6 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 6)) = true := by
  decide +kernel
#print axioms coreFlatten83_6
#print axioms coreCheck83_6
end Erdos883Verified
