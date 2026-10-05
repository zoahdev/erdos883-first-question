import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_63 :
    (List.ofFn coreChunks680_63).flatten =
      (coreData680.take (coreResources680 63).q).drop 122 := by
  decide +kernel

theorem coreCheck680_63 :
    ∀ c : Fin 1, (coreChunks680_63 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 63)) = true := by
  decide +kernel
#print axioms coreFlatten680_63
#print axioms coreCheck680_63
end Erdos883Verified
