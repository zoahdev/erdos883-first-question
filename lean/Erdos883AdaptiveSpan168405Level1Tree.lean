import Erdos883AdaptiveSpan168405Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength168405_1 : adaptiveNumericSpans168405_1.length = 746 := by decide +kernel
theorem adaptiveSpanEvenCache168405_1 : adaptiveSpanEven168405_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain168405_1 : adaptiveSpanEven168405_1.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanEvenEntries168405_1 : adaptiveSpanEven168405_1.spans = coreEvenSpans 84203 0 adaptiveNumericSpans168405_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache168405_1 : adaptiveSpanWhole168405_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain168405_1 : adaptiveSpanWhole168405_1.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanWholeEntries168405_1 : adaptiveSpanWhole168405_1.spans = coreWholeSpans 0 adaptiveNumericSpans168405_1 := by
  decide +kernel
end Erdos883Verified
