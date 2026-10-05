import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_73 :
    (List.ofFn coreChunks509_73).flatten =
      (coreData509.take (coreResources509 73).q).drop 137 := by
  decide +kernel

theorem coreCheck509_73 :
    ∀ c : Fin 1, (coreChunks509_73 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 73)) = true := by
  decide +kernel
#print axioms coreFlatten509_73
#print axioms coreCheck509_73
end Erdos883Verified
