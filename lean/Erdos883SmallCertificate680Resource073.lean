import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_73 :
    (List.ofFn coreChunks680_73).flatten =
      (coreData680.take (coreResources680 73).q).drop 137 := by
  decide +kernel

theorem coreCheck680_73 :
    ∀ c : Fin 1, (coreChunks680_73 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 73)) = true := by
  decide +kernel
#print axioms coreFlatten680_73
#print axioms coreCheck680_73
end Erdos883Verified
