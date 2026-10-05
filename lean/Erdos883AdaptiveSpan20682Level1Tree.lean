import Erdos883AdaptiveSpan20682Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength20682_1 : adaptiveNumericSpans20682_1.length = 430 := by decide +kernel
theorem adaptiveSpanEvenCache20682_1 : adaptiveSpanEven20682_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain20682_1 : adaptiveSpanEven20682_1.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanEvenEntries20682_1 : adaptiveSpanEven20682_1.spans = coreEvenSpans 10341 0 adaptiveNumericSpans20682_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache20682_1 : adaptiveSpanWhole20682_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain20682_1 : adaptiveSpanWhole20682_1.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanWholeEntries20682_1 : adaptiveSpanWhole20682_1.spans = coreWholeSpans 0 adaptiveNumericSpans20682_1 := by
  decide +kernel
end Erdos883Verified
