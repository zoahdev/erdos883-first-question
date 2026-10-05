import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_111 :
    (List.ofFn coreChunks680_111).flatten =
      (coreData680.take (coreResources680 111).q).drop 223 := by
  decide +kernel

theorem coreCheck680_111 :
    ∀ c : Fin 1, (coreChunks680_111 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 111)) = true := by
  decide +kernel
#print axioms coreFlatten680_111
#print axioms coreCheck680_111
end Erdos883Verified
