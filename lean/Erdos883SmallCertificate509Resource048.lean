import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_48 :
    (List.ofFn coreChunks509_48).flatten =
      (coreData509.take (coreResources509 48).q).drop 94 := by
  decide +kernel

theorem coreCheck509_48 :
    ∀ c : Fin 1, (coreChunks509_48 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 48)) = true := by
  decide +kernel
#print axioms coreFlatten509_48
#print axioms coreCheck509_48
end Erdos883Verified
