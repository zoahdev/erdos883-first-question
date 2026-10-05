import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_81 :
    (List.ofFn coreChunks509_81).flatten =
      (coreData509.take (coreResources509 81).q).drop 159 := by
  decide +kernel

theorem coreCheck509_81 :
    ∀ c : Fin 1, (coreChunks509_81 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 81)) = true := by
  decide +kernel
#print axioms coreFlatten509_81
#print axioms coreCheck509_81
end Erdos883Verified
