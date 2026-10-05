import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_98 :
    (List.ofFn coreChunks618_98).flatten =
      (coreData618.take (coreResources618 98).q).drop 251 := by
  decide +kernel

theorem coreCheck618_98 :
    ∀ c : Fin 1, (coreChunks618_98 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 98)) = true := by
  decide +kernel
#print axioms coreFlatten618_98
#print axioms coreCheck618_98
end Erdos883Verified
