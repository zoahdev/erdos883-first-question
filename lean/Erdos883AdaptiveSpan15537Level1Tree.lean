import Erdos883AdaptiveSpan15537Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength15537_1 : adaptiveNumericSpans15537_1.length = 402 := by decide +kernel
theorem adaptiveSpanEvenCache15537_1 : adaptiveSpanEven15537_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain15537_1 : adaptiveSpanEven15537_1.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanEvenEntries15537_1 : adaptiveSpanEven15537_1.spans = coreEvenSpans 7769 0 adaptiveNumericSpans15537_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache15537_1 : adaptiveSpanWhole15537_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain15537_1 : adaptiveSpanWhole15537_1.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanWholeEntries15537_1 : adaptiveSpanWhole15537_1.spans = coreWholeSpans 0 adaptiveNumericSpans15537_1 := by
  decide +kernel
end Erdos883Verified
