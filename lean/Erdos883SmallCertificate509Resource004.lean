import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_4 :
    (List.ofFn coreChunks509_4).flatten =
      (coreData509.take (coreResources509 4).q).drop 63 := by
  decide +kernel

theorem coreCheck509_4 :
    ∀ c : Fin 1, (coreChunks509_4 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 4)) = true := by
  decide +kernel
#print axioms coreFlatten509_4
#print axioms coreCheck509_4
end Erdos883Verified
