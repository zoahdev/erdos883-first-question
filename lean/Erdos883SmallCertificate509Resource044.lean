import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_44 :
    (List.ofFn coreChunks509_44).flatten =
      (coreData509.take (coreResources509 44).q).drop 88 := by
  decide +kernel

theorem coreCheck509_44 :
    ∀ c : Fin 1, (coreChunks509_44 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 44)) = true := by
  decide +kernel
#print axioms coreFlatten509_44
#print axioms coreCheck509_44
end Erdos883Verified
