import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_15 :
    (List.ofFn coreChunks509_15).flatten =
      (coreData509.take (coreResources509 15).q).drop 104 := by
  decide +kernel

theorem coreCheck509_15 :
    ∀ c : Fin 1, (coreChunks509_15 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 15)) = true := by
  decide +kernel
#print axioms coreFlatten509_15
#print axioms coreCheck509_15
end Erdos883Verified
