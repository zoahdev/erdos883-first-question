import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_20 :
    (List.ofFn coreChunks509_20).flatten =
      (coreData509.take (coreResources509 20).q).drop 110 := by
  decide +kernel

theorem coreCheck509_20 :
    ∀ c : Fin 1, (coreChunks509_20 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 20)) = true := by
  decide +kernel
#print axioms coreFlatten509_20
#print axioms coreCheck509_20
end Erdos883Verified
